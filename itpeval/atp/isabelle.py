"""Find proof suggestions with Isabelle and replay them through its locked verifier."""

from __future__ import annotations

import re
from dataclasses import dataclass, replace
from pathlib import Path
from tempfile import TemporaryDirectory
from threading import Event

from itpeval.backends.projects import project_file
from itpeval.core.types import Budgets, TaskSpec, VerificationEvidence
from itpeval.core.records import Record
from itpeval.environments import PreparedProject
from itpeval.environments.cache import sha256
from itpeval.runtime.process import run_process
from itpeval.verification.fragments import permitted
from itpeval.verification.policies import reviewed, validate_inputs
from itpeval.verification.service import verify

from .search import SOLVERS, SolverBuild, SolverProcess, _fingerprint, _isabelle_component, native_environment


_SESSION = re.compile(r'^\s*session\s+(?:"[^"]+"|[\w.-]+)\s*=\s*(?:"([\w.-]+)"|([\w.-]+))\s*\+', re.MULTILINE)
_MESSAGE = re.compile(r'^Output \(line (\d+) of "([^"]+)"\):\s*$', re.MULTILINE)
_TIMING = re.compile(r"\s+\((?:\d+(?:\.\d+)? ?(?:ms|s)|<\s*1\s*ms)\)\s*$")
_FACT_POOL = re.compile(r"^Selected (\d+)(?: ([\w-]+))? facts?:[ \t]*", re.MULTILINE)


@dataclass(frozen=True)
class SuggestedProof(Record):
    text: str
    disposition: str
    evidence: VerificationEvidence | None = None


@dataclass(frozen=True)
class PremisePool(Record):
    fact_filter: str | None
    declared_count: int
    facts: tuple[str, ...] | None


@dataclass(frozen=True)
class HammerEvidence(Record):
    environment_id: str
    task_id: str
    target: str
    solver: SolverBuild
    search_budgets: Budgets
    solver_timeout_s: int
    search: SolverProcess
    search_outcome: str
    suggestions: tuple[SuggestedProof, ...]
    trace_premises: bool = False
    premise_pools: tuple[PremisePool, ...] = ()
    replay_limit: int | None = None
    search_diagnostic: str | None = None

    @property
    def checked_proof(self) -> SuggestedProof | None:
        return next((proof for proof in self.suggestions if proof.disposition == "accepted"), None)


def _search_messages(log: str, source: Path, line: int, solver: str):
    messages = list(_MESSAGE.finditer(log))
    found = False
    proofs = {}
    pools = []
    for index, match in enumerate(messages):
        if int(match[1]) != line or Path(match[2]) != source:
            continue
        end = messages[index + 1].start() if index + 1 < len(messages) else len(log)
        message = log[match.end():end].strip()
        if message.startswith(f"{solver} found a proof"):
            found = True
        prefix = f"{solver}: Try this: "
        if message.startswith(prefix):
            suggestion = _TIMING.sub("", " ".join(message[len(prefix):].splitlines())).strip()
            proofs[suggestion] = None
        headers = list(_FACT_POOL.finditer(message))
        for pool_index, header in enumerate(headers):
            last = headers[pool_index + 1].start() if pool_index + 1 < len(headers) else len(message)
            count = int(header[1])
            facts = tuple(message[header.end():last].split())
            # Native rendering may put several words in one fact label. Keep
            # the count and the transcript when it cannot be split unambiguously.
            pools.append(PremisePool(header[2], count, facts if len(facts) == count else None))
    return found, list(proofs), tuple(pools)


def run_sledgehammer(task: TaskSpec, *, prepared: PreparedProject, solver: str = "e",
                     search_timeout_s: float | None = None, solver_timeout_s: int = 5,
                     replay_limit: int = 4, trace_premises: bool = True,
                     cancel: Event | None = None) -> HammerEvidence:
    """Search at the original Isabelle proof slot and verify authorized suggestions.

    Search uses a local solver in a private session. Replay consults the same
    checker, proof constraints, and obligations as any other document edit.
    """
    if (task.prover != "isabelle" or prepared.spec.prover != "isabelle"
            or task.operation != "proof_completion" or not task.manifest_path
            or task.environment_id != prepared.environment_id or prepared.spec.checking_profile != "strict"
            or not reviewed(task, prepared)):
        raise ValueError("Sledgehammer requires a reviewed Isabelle completion task in its locked project")
    if solver not in SOLVERS:
        raise ValueError("Sledgehammer supports the local E and Vampire components")
    if type(solver_timeout_s) is not int or solver_timeout_s <= 0 or type(replay_limit) is not int or replay_limit <= 0:
        raise ValueError("positive solver timeout and replay limits are required")
    limits = task.budgets
    if search_timeout_s is not None:
        if not 0 < search_timeout_s <= limits.timeout_s:
            raise ValueError("search timeout must be positive and fit the task's wall budget")
        limits = replace(limits, timeout_s=search_timeout_s)
    if solver_timeout_s > limits.timeout_s:
        raise ValueError("solver timeout must fit the supervised search budget")
    prepared.validate()
    validate_inputs(task, task.artifact)
    if task.artifact.entrypoint != task.editable_regions[0].path:
        raise ValueError("the editable theory must be the entrypoint")

    isabelle_root = prepared.prefix / "isabelle"
    isabelle = isabelle_root / "bin/isabelle"
    root_name = next((item.path for item in task.artifact.files if item.path == "ROOT"), None)
    if root_name is None:
        raise ValueError("an Isabelle task must include its session ROOT file")
    root = project_file(prepared.project, root_name).read_text(encoding="utf-8")
    parents = _SESSION.findall(root)
    if len(parents) != 1:
        raise ValueError("Sledgehammer needs a project ROOT with one native session and a parent heap")
    parent = next(value for value in parents[0] if value)

    with TemporaryDirectory(prefix="itpeval-hammer-") as temp:
        work = Path(temp)
        home, source = work / "home", work / "project"
        home.mkdir()
        verbosity = "true" if trace_premises else "false"
        command = f"sledgehammer [provers = {solver}, timeout = {solver_timeout_s}, verbose = {verbosity}]\n"
        region = task.editable_regions[0]
        for item in task.artifact.files:
            target = source / item.path
            target.parent.mkdir(parents=True, exist_ok=True)
            original = project_file(prepared.project, item.path).read_bytes()
            if item.path == region.path:
                # Insert Sledgehammer before the proof slot so it sees the original goal.
                search_line = original[:region.start].count(b"\n") + 1
                original = original[:region.start] + command.encode("ascii") + original[region.start:]
            target.write_bytes(original)
        binary = _isabelle_component(solver, isabelle, home).resolve(strict=True)
        if not binary.is_relative_to((isabelle_root / "dist").resolve()):
            raise ValueError(f"{solver} must come from the Isabelle distribution covered by the lock")
        build = _fingerprint(solver, binary, home)
        entry = source / task.artifact.entrypoint
        theory = Path(task.artifact.entrypoint).with_suffix("").as_posix()
        # With parallel proofs enabled, a failing starter can cancel the
        # preceding diagnostic command before Sledgehammer returns suggestions.
        cmd = [str(isabelle), "process_theories", "-D", str(source), "-O", "-l", parent,
               "-o", "quick_and_dirty=false", "-o", "threads=2", "-o", "parallel_proofs=0", theory]
        native = run_process(cmd, cwd=source, env=native_environment(home), cancel=cancel,
                             timeout_s=limits.timeout_s, max_log_bytes=limits.max_log_bytes,
                             cpu_seconds=limits.cpu_seconds, memory_bytes=limits.memory_bytes)
        if sha256(binary) != build.executable_sha256:
            raise ValueError("automated prover executable changed during proof search")
        output = SolverProcess.from_process(native)
        found, candidates, pools = _search_messages(native.stdout, entry, search_line, solver)
    suggestions = []
    search_diagnostic = None
    if native.outcome != "exited":
        search_outcome = native.outcome
    elif native.truncated:
        search_outcome = "output_truncated"
    elif native.returncode and 'Unknown Isabelle tool: "process_theories"' in native.stdout + native.stderr:
        search_outcome = "unsupported_toolchain"
        search_diagnostic = "ATP-assisted replay requires Isabelle process_theories (tested on Isabelle2026)"
    elif native.returncode and not (found or candidates):
        search_outcome = "search_error"
    else:
        # A rejected starter can still leave a usable suggestion.
        search_outcome = "proof_found" if found or candidates else "no_proof_reported"
        attempted = 0
        terminal_verdict = False
        for candidate in candidates:
            if not permitted(task.prover, candidate, task.allowed_edits, task.proof_atoms):
                suggestions.append(SuggestedProof(candidate, "outside_task_policy"))
            elif terminal_verdict:
                suggestions.append(SuggestedProof(candidate, "replay_already_finished"))
            elif attempted == replay_limit:
                suggestions.append(SuggestedProof(candidate, "replay_budget_exhausted"))
            else:
                attempted += 1
                replay = verify(task, candidate, prepared=prepared, cancel=cancel)
                terminal_verdict = replay.task_success is not False
                disposition = "accepted" if replay.task_success else (
                    "rejected" if replay.task_success is False else replay.execution_outcome)
                suggestions.append(SuggestedProof(candidate, disposition, replay))
    return HammerEvidence(prepared.environment_id, task.task_id, task.targets[0], build,
                          limits, solver_timeout_s, output, search_outcome, tuple(suggestions),
                          trace_premises, pools, replay_limit, search_diagnostic)
