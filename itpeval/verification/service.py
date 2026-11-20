"""Check constrained proof completions or fixed artifacts in a fresh workspace."""
from __future__ import annotations

import os
import re
import subprocess
import sys
from dataclasses import replace
from pathlib import Path
from threading import Event
from time import monotonic
from typing import TYPE_CHECKING

from itpeval.backends.registry import ROOT, get_backend
from itpeval.core.records import digest
from itpeval.core.types import Artifact, TaskSpec, VerificationEvidence
from itpeval.runtime.checker import execute_checker
from itpeval.runtime.process import run_process
from itpeval.runtime.workspace import attempt_workspace

from .policies import assemble, candidate_from_bytes, reviewed_document_template, validate_inputs

if TYPE_CHECKING:
    from itpeval.environments import PreparedProject


_ENV_FAILURE = re.compile(
    r"run install\.sh|not found in opam|environment was found|did not produce an error report|"
    r"permission denied|operation not permitted|bad system call|GLIBC_[\d.]+' not found|"
    r"executable not found|failed to load|could not open.*heap", re.I)
_CRASH = re.compile(
    r"Traceback \(most recent call last\)|fatal error:|segmentation fault|internal error|"
    r"Unhandled .*Exception|no space left on device|bus error|stack overflow|core dumped", re.I)
_REJECTION = re.compile(
    r"\bError:|\?Error|ACL2 Error|FAILED \*+|reported verification errors|"
    r"(?:type|unification) mismatch|unsolved metas|not in scope|"
    r"failed to (?:apply|finish)|proof failed|unsolved goals|"
    r"cannot find a proof|No applicable tactic|Tactic failure|"
    r"exception.*Failure|NO_TAC|unfinished|unproved|is not a valid|"
    r"when checking|do not match|has not been proved|Unsolved interaction", re.I)


_OPEN_PROOF = re.compile(
    r"\bunsolved goals\b|attempt to save an incomplete proof|"
    r"^\s*[\w?'-]+\.{2,}unfinished\s+\[|"
    r"the following \$p statement\(s\) were not proved", re.I | re.M)


def _reported_assumptions(task, stdout):
    if task.prover == "lean4":
        name = re.escape(task.targets[0])
        matches = re.findall(r"^'" + name
                             + r"' (?:does not depend on any axioms|depends on axioms: \[([^\]]*)\])",
                             stdout, re.M)
        if matches:
            return {atom for axiom_list in matches for atom in axiom_list.split(", ") if atom}
    elif re.search(r"^Axioms:\s*$", stdout, re.M):
        # A file may print assumptions for more than one declaration. Check every
        # reported dependency so an unrelated closed theorem cannot mask an axiom.
        names = set()
        for section in re.split(r"^Axioms:\s*$", stdout, flags=re.M)[1:]:
            found = re.findall(r"^([\w.']+)(?: :|$)", section, re.M)
            if not found:
                return None
            names.update(found)
        return names
    elif re.search(r"^Closed under the global context\s*$", stdout, re.M):
        return set()
    return None


def verify(task: TaskSpec, candidate: str | None = None, *, prepared: PreparedProject,
           cancel: Event | None = None, retain_dir: Path | None = None,
           metamath_base: str | None = None) -> VerificationEvidence:
    """Check a proof fragment, or a task's fixed artifact when it takes no fragment."""
    return _verify(task, candidate, None, prepared, cancel, retain_dir, metamath_base)


def verify_document(task: TaskSpec, document: Artifact | str | bytes, *, prepared: PreparedProject,
                    cancel: Event | None = None, retain_dir: Path | None = None,
                    metamath_base: str | None = None) -> VerificationEvidence:
    """Check a full revision. Text or bytes replace the entrypoint and retain locked siblings.

    Artifact inputs must supply the complete file set. The proof slot can be sent
    in either the original source or the instrumented source returned by assemble().
    """
    if isinstance(document, Artifact):
        submitted = document
    elif isinstance(document, (str, bytes)):
        files = {entry.path: entry.data for entry in task.artifact.files}
        files[task.artifact.entrypoint] = document.encode() if isinstance(document, str) else document
        submitted = Artifact.from_files(task.artifact.entrypoint, files)
    else:
        raise TypeError("document must be an Artifact, str or bytes")
    return _verify(task, None, submitted, prepared, cancel, retain_dir, metamath_base)


def _document_slot(task, submitted, original_template):
    """Check file identity and fixed bytes and recover the editable bytes."""
    trusted = {entry.path: entry.data for entry in task.artifact.files}
    actual = {entry.path: entry.data for entry in submitted.files}
    if submitted.entrypoint != task.artifact.entrypoint or actual.keys() != trusted.keys():
        raise ValueError("submitted entrypoint or file set differs from the locked task")
    if task.operation != "proof_completion":
        if actual != trusted:
            raise ValueError("submitted files differ from the fixed artifact")
        return None
    region, = task.editable_regions
    source = actual.pop(region.path)
    instrumented = trusted.pop(region.path)
    if actual != trusted:
        raise ValueError("a fixed file outside the editable proof differs from the locked task")
    for template in (instrumented, original_template):
        prefix, suffix = template[:region.start], template[region.end:]
        end = len(source) - len(suffix)
        if end >= len(prefix) and source.startswith(prefix) and source.endswith(suffix):
            return source[len(prefix):end]
    raise ValueError("submitted document changes fixed bytes outside the editable proof")


def _verify(task, candidate, submitted, prepared, cancel, retain_dir, metamath_base):
    artifact = submitted if submitted is not None else task.artifact
    workspace = None
    proof = task.operation == "proof_completion"

    def result(execution, checker="not_run", success=None, *, message="", process=None,
               completion="unknown", preservation="unchecked", obligations=(), references=()):
        if submitted is not None:
            references = (*references, "submitted_artifact:" + submitted.artifact_id)
        return VerificationEvidence(
            task.task_id, task.environment_id, artifact.artifact_id, execution, checker, success,
            preservation, completion, obligations, process.duration_ms if process else 0,
            process.returncode if process else None, process.stdout if process else "",
            (process.stderr if process else "") + message, references, workspace,
            process.peak_process_rss_bytes if process else None, process.cpu_time_s if process else None,
            process.truncated if process else False)

    if metamath_base is not None and (task.prover != "metamath" or not proof):
        return result("unsupported_operation", message="a verified base requires a Metamath proof completion")
    if task.operation not in ("check_artifact", "statement", "proof_completion"):
        return result("unsupported_operation", message=f"unsupported operation: {task.operation}")
    if prepared.environment_id != task.environment_id or prepared.spec.prover != task.prover:
        return result("unavailable_environment", message="task and prepared environment identities differ")
    adapter = getattr(prepared, "adapter", None)
    if adapter is None:
        try:
            get_backend(task.prover)
        except (OSError, ValueError) as exc:
            return result("unsupported_operation", message=str(exc))
    if adapter is not None and (not proof or not task.is_detached_certificate or not task.manifest_path):
        return result("unsupported_operation", message="typed adapters require a reviewed detached certificate task")
    if proof and prepared.spec.checking_profile != "strict":
        return result("unsupported_operation", message="proof completion requires the strict checking profile")
    if proof and task.prover == "lean4":
        # Compiler/kernel alterations are outside this proof profile. These settings
        # change only resource bounds and presentation of normal elaboration.
        options = dict(prepared.spec.options)
        if any(k not in {"maxHeartbeats", "maxRecDepth", "synthInstance.maxHeartbeats"}
               or not re.fullmatch(r"[0-9]+", v) for k, v in options.items()):
            return result("unsupported_operation", message="unsupported Lean option in strict proof profile")
    if cancel is not None and cancel.is_set():
        return result("cancelled")
    try:
        prepared.validate()
    except (OSError, ValueError, RuntimeError, subprocess.SubprocessError) as exc:
        return result("unavailable_environment", message=str(exc))
    original_template = None
    if proof:
        try:
            original_template = reviewed_document_template(task, prepared)
            if original_template is None:
                return result("unsupported_operation", message="no reviewed target witness for this proof task")
        except (OSError, ValueError, TypeError, KeyError) as exc:
            return result("unsupported_operation", message=str(exc))
    try:
        validate_inputs(task, task.artifact)
    except ValueError as exc:
        return result("unsupported_operation", message=str(exc))
    if submitted is not None:
        try:
            slot = _document_slot(task, submitted, original_template)
        except ValueError as exc:
            return result("not_run", "policy_rejected", False, message=str(exc),
                          completion="incomplete", preservation="violated")
        if slot is not None:
            try:
                candidate = candidate_from_bytes(task, slot)
            except UnicodeDecodeError:
                return result("not_run", "policy_rejected", False, message="proof slot requires UTF-8",
                              completion="incomplete", preservation="preserved")
    if proof and (candidate is None or not candidate.strip()):
        return result("not_run", "incomplete", False, message="No proof completion was supplied",
                      completion="incomplete", preservation="preserved")
    try:
        artifact = assemble(task, candidate)
    except ValueError as exc:
        return result("not_run", "policy_rejected", False, message=str(exc), completion="incomplete",
                      preservation="preserved" if submitted is not None else "unchecked")
    if task.prover == "hol4" and not artifact.entrypoint.endswith("Script.sml"):
        return result("unsupported_operation", message="native HOL4 task requires a theory Script.sml entrypoint")
    if task.prover == "isabelle" and "ROOT" not in {entry.path for entry in artifact.files}:
        return result("unsupported_operation", message="native Isabelle task requires a ROOT session")
    try:
        with attempt_workspace(retain_dir) as attempt:
            workspace = str(attempt) if retain_dir is not None else None
            source = attempt / "source"
            artifact.materialize(source)
            if adapter is not None:
                from .external import run_detached_checker

                process, receipt = run_detached_checker(task, prepared, artifact, source, attempt, cancel)
                if process.outcome != "exited":
                    return result(process.outcome, process=process)
                if receipt is None:
                    return result("backend_error", "insufficient_evidence", process=process,
                                  message="\nMissing or mismatched detached checker receipt")
                try:
                    prepared.validate()
                except (OSError, ValueError, RuntimeError) as exc:
                    return result("unavailable_environment", process=process, message=str(exc))
                witness = receipt.to_dict()
                witness.pop("detail", None)
                witness["assumptions"] = sorted(set(receipt.assumptions))
                refs = (f"{task.prover}:certificate:{digest(witness)}",)
                if receipt.status != "accepted":
                    return result("exited", receipt.status, False, preservation="preserved",
                                  completion="incomplete", references=refs, process=process)
                unauthorized = set(receipt.assumptions) - set(task.allowed_assumptions)
                if unauthorized:
                    return result("exited", "policy_rejected", False, preservation="preserved",
                                  completion="incomplete", references=refs, process=process,
                                  message="\nUnauthorized premises: " + ", ".join(sorted(unauthorized)))
                return result("exited", "accepted", True, preservation="preserved", completion="proved",
                              obligations=tuple((name, "discharged") for name in task.obligations),
                              references=refs, process=process)
            if metamath_base is not None:
                from itpeval.backends.metamath.base import (
                    BaseVerificationError,
                    _verify_extension,
                )
                try:
                    process, checker, build = _verify_extension(task, artifact, prepared, metamath_base,
                                                               stage=source, cancel=cancel)
                except BaseVerificationError as exc:
                    outcome = exc.check.outcome
                    return result(outcome if outcome != "exited" else "unavailable_environment",
                                  message="\n" + str(exc), process=exc.check)
                except (ValueError, OSError) as exc:
                    return result("unsupported_operation", message=str(exc))
                refs = (f"metamath:verified-base:{build.base_id}",
                        "base_verification_cache_hit" if build.cache_hit else "base_verified_this_call",
                        f"metamath:verify-proof:{task.targets[0]}")
                if checker is None:
                    return result(process.outcome if process.outcome != "exited" else "backend_error",
                                  "insufficient_evidence", process=process, references=refs)
                success = checker == "accepted"
                return result("exited", checker, success,
                              completion="proved" if success else "incomplete", preservation="preserved",
                              obligations=tuple((name, "discharged") for name in task.obligations) if success else (),
                              references=refs, process=process)
            scratch = attempt / "tmp"
            scratch.mkdir()
            # Only inherited base OS settings and explicitly locked adapter options
            # enter a strict check. Legacy task selectors cannot choose the operation.
            env = {k: os.environ[k] for k in ("HOME", "LANG", "LC_ALL", "PATH", "USER", "LOGNAME")
                   if k in os.environ}
            env.update(prepared.environment)
            env.update(ITPEVAL_PREFIX=str(prepared.prefix), ITPEVAL_TASK_DIR=str(source),
                       ITPEVAL_OPERATION=task.operation, ITPEVAL_PYTHON=sys.executable, TMPDIR=str(scratch))
            if proof:
                env["ITPEVAL_EXPECT_TARGET"] = task.targets[0]
            if task.dependency_sources:
                env["ITPEVAL_LOCAL_SOURCES"] = "\n".join(task.dependency_sources)
            if task.prover in {"acl2", "agda", "metamath", "mizar", "pvs", "lean4", "rocq", "hol-light"}:
                env["ITPEVAL_TASK_FILE"] = artifact.entrypoint
            started = monotonic()
            process = execute_checker(
                ROOT / "provers" / task.prover / "check.sh", source, env, timeout_s=task.budgets.timeout_s, cancel=cancel,
                max_log_bytes=task.budgets.max_log_bytes, memory_bytes=task.budgets.memory_bytes,
                cpu_seconds=task.budgets.cpu_seconds)
            if proof and task.prover == "metamath" and process.outcome == "exited" and not process.returncode:
                target = task.targets[0]
                remaining = max(.001, task.budgets.timeout_s - (monotonic() - started))
                trace = run_process([str(prepared.prefix / "metamath/bin/metamath"), "set width 9999",
                                     f'read "{artifact.entrypoint}"', f"show trace_back {target} /axioms", "exit"],
                                    cwd=source, env=env, timeout_s=remaining, cancel=cancel,
                                    max_log_bytes=task.budgets.max_log_bytes,
                                    memory_bytes=task.budgets.memory_bytes, cpu_seconds=task.budgets.cpu_seconds)
                # Preserve evidence of both verification and the axiom query.
                def tail(text):
                    return text.encode()[-task.budgets.max_log_bytes:].decode(errors="replace")
                combined = process.stdout + "\n" + trace.stdout
                process = replace(trace, stdout=tail(combined), stderr=tail(process.stderr + trace.stderr),
                                  truncated=trace.truncated or process.truncated or len(combined.encode()) > task.budgets.max_log_bytes,
                                  duration_ms=process.duration_ms + trace.duration_ms,
                                  peak_process_rss_bytes=max(trace.peak_process_rss_bytes or 0, process.peak_process_rss_bytes or 0),
                                  cpu_time_s=(trace.cpu_time_s or 0) + (process.cpu_time_s or 0))
                if trace.outcome == "exited" and not trace.returncode:
                    deps = re.search(r'Statement "' + re.escape(target) + r'" assumes the following axioms'
                                     r' \(\$a statements\):\n(.*?)\nMM>', trace.stdout, re.S)
                    if deps is None:
                        return result("backend_error", "insufficient_evidence", process=process,
                                      message="\nMissing Metamath axiom dependency report")
                    axioms = set() if deps[1].strip() == "(None)" else set(deps[1].split())
                    unauthorized = axioms - set(task.allowed_assumptions)
                    if unauthorized:
                        return result("exited", "policy_rejected", False, completion="incomplete", process=process,
                                      message="\nUnauthorized Metamath axioms: " + ", ".join(sorted(unauthorized)))
    except OSError as exc:
        return result("unavailable_environment", message=str(exc))
    if process.outcome != "exited":
        return result(process.outcome, process=process)
    logs = process.stdout + "\n" + process.stderr
    if process.returncode:
        if process.returncode == 124 or "exited with status 124" in logs:
            return result("timeout", process=process)
        if _ENV_FAILURE.search(logs) or process.returncode in (126, 127):
            return result("unavailable_environment", process=process)
        if re.search(r"out of memory|memory exhausted|cannot allocate memory", logs, re.I):
            return result("resource_exhausted", process=process)
        if _CRASH.search(logs):
            return result("backend_error", process=process)
        if proof and _OPEN_PROOF.search(logs):
            return result("exited", "incomplete", False, completion="incomplete",
                          process=process, preservation="preserved")
        if _REJECTION.search(logs):
            return result("exited", "rejected", False, completion="incomplete" if proof else "unchecked",
                          process=process, preservation="preserved" if proof else "unchecked")
        return result("backend_error", process=process)
    if proof:
        if task.prover == "pvs":
            totals = re.search(r"^Grand Totals:\s+(\d+) proofs?, (\d+) attempted, (\d+) succeeded",
                               process.stdout, re.MULTILINE)
            proved = set(re.findall(r"^\s*([\w?'-]+)\.{2,}proved - complete\b", process.stdout, re.MULTILINE))
            if (totals is None or len(set(totals.groups())) != 1 or not proved
                    or not set(task.obligations).issubset(proved)):
                return result("backend_error", "insufficient_evidence", process=process,
                              message="\nMissing PVS target or TCC completion summary")
        if task.prover in ("lean4", "rocq"):
            assumptions = _reported_assumptions(task, process.stdout)
            if assumptions is None:
                return result("backend_error", "insufficient_evidence", process=process,
                              message="\nMissing native assumptions report")
            if "sorryAx" in assumptions or not assumptions.issubset(task.allowed_assumptions):
                return result("exited", "policy_rejected", False, completion="incomplete",
                              process=process, message="\nUnauthorized dependencies: "
                              + ", ".join(sorted((assumptions - set(task.allowed_assumptions)) | (assumptions & {"sorryAx"}))))
        expected = task.native_receipt
        if task.prover in {"isabelle", "hol4", "agda"}:
            expected = "ITPEVAL_TARGET " + task.targets[0]
        if expected is not None and expected not in process.stdout:
            return result("backend_error", "insufficient_evidence", process=process,
                          message="\nMissing checker evidence: " + expected)
        return result("exited", "accepted", True, preservation="preserved", completion="proved",
                      obligations=tuple((name, "discharged") for name in task.obligations),
                      references=(expected or f"{task.prover}:native-check",), process=process)
    return result("exited", "accepted", True, completion="statement_accepted" if
                  task.operation == "statement" else "artifact_accepted", process=process)
