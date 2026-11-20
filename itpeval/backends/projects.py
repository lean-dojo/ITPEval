"""Construct proof tasks from reviewed manifests in a locked research project."""
from __future__ import annotations

import json
import re
from dataclasses import dataclass, field
from pathlib import Path

from itpeval.core.records import Record
from itpeval.core.types import Artifact, Budgets, EditableRegion, TaskSpec, logical_path


@dataclass(frozen=True)
class CompletionManifest(Record):
    """The anchor identifies a native declaration and the slot identifies its proof bytes.

    The project owner reviews proof fragments and atoms as executable code in the
    specified environment. The optional observer is inserted after a fixed source
    anchor, separately from the editable proof.
    """
    entrypoint: str
    files: tuple[str, ...]
    anchor: str
    target: str
    statement: str
    proof_slot: str
    allowed_edits: tuple[str, ...]
    proof_atoms: tuple[str, ...] = ()
    allowed_assumptions: tuple[str, ...] = ()
    obligations: tuple[str, ...] = ()
    observer_anchor: str | None = None
    budgets: Budgets = field(default_factory=Budgets)
    dependency_sources: tuple[str, ...] = ()


def project_file(root: Path, name: str) -> Path:
    normalized = root.resolve(strict=True)
    target = (normalized / logical_path(name)).resolve(strict=True)
    if not target.is_relative_to(normalized) or not target.is_file():
        raise ValueError(f"expected a regular file inside the prepared project: {name!r}")
    return target


def _observer(prover, m):
    name, statement = m.target, m.statement
    if not re.fullmatch(r"[A-Za-z][a-zA-Z_0-9.'-]*", name):
        raise ValueError("invalid prover target identifier")
    if not statement.strip():
        raise ValueError("the manifest requires a native statement")
    if prover == "lean4":
        return f"example : {statement} := @{name}\n#print axioms {name}", None
    if prover == "rocq":
        return f"Check ({name} : {statement}).\nPrint Assumptions {name}.", None
    if prover == "isabelle":
        return (f'ML \\<open>val _ = if Thm_Deps.has_skip_proof [@{{thm {name}}}] then error "incomplete target" '
                f'else File.write (Path.append (Resources.master_directory @{{theory}}) '
                f'(Path.basic "itpeval-witness-{name}")) "{name}"\\<close>'), None
    if prover == "hol-light":
        return (f"let () = if hyp {name} = [] && aconv (concl {name}) `{statement}`\n"
                f'  then print_endline "ITPEVAL_TARGET_CLOSED" else failwith "target mismatch";;'
                ), "ITPEVAL_TARGET_CLOSED"
    if prover == "hol4":
        return (f"val _ = if null (hyp {name}) andalso aconv (concl {name}) ``{statement}``\n"
                f'  then let val out = TextIO.openOut "itpeval-target-witness" '
                f'in TextIO.output (out, "{name}"); TextIO.closeOut out end '
                f'else raise Fail "target mismatch";'), None
    if prover == "acl2":
        return (f"(assert-event (getpropc '{name} 'theorem nil (w state)))\n"
                f"(value-triple :itpeval-target-admitted)"), ":ITPEVAL-TARGET-ADMITTED"
    if prover == "metamath":
        return "", "All proofs in the database were verified"
    if prover in ("agda", "mizar", "pvs"):
        return "", None
    raise ValueError(f"unsupported prover: {prover}")


def _declared_statement(prover, tail, local_name):
    # These profiles identify statements by an exact source locator. Other
    # backends ask the kernel to equate the manifest type and the target type.
    if prover == "metamath":
        match = re.fullmatch(r"\s*\$p\s+(.+?)\s+\$=\s*", tail, re.S)
    elif prover == "pvs":
        match = re.fullmatch(r"\s*:\s*(?:LEMMA|THEOREM)\s+(.+?)\s*\n\s*%\|-.*", tail, re.I | re.S)
    elif prover == "agda":
        match = re.fullmatch(r"\s*:\s*(.+?)\n[ \t]*" + local_name + r"(?![\w'-]).*", tail, re.S)
    elif prover == "mizar":
        match = re.fullmatch(r"\s*:\s*(.+?)(?:\s+proof\b.*)?", tail.strip(), re.I | re.S)
    elif prover == "isabelle":
        match = re.fullmatch(r"\s*:\s*(.+?)\s*", tail, re.S)
    elif prover == "acl2":
        from itpeval.backends.acl2.syntax import _forms
        formula = tail.lstrip()
        if formula.startswith("("):
            form = next(_forms(formula.encode()), None)
            if form:
                return form[2].decode()
        else:
            atom = re.match(r"[^()\s]+", formula)
            if atom:
                return atom[0]
        return None
    else:
        return None
    return match[1].strip() if match else None


def _locate(m, source, prover):
    anchor, proof = m.anchor.encode(), m.proof_slot.encode()
    if not anchor or source.count(anchor) != 1 or not proof or anchor.count(proof) != 1:
        raise ValueError("expected a unique native declaration and proof slot")
    before = m.anchor.split(m.proof_slot)[0]
    local_name = re.escape(m.target.rsplit(".", 1)[-1])
    heads = {"lean4": r"(?:theorem|lemma)\s+", "rocq": r"(?:Theorem|Lemma)\s+",
             "isabelle": r"(?:theorem|lemma)\s+", "acl2": r"\(defthm[d]?\s+",
             "hol4": r"val\s+", "hol-light": r"let\s+", "agda": r"^\s*",
             "metamath": r"^\s*", "mizar": r"theorem\s+", "pvs": r"^\s*"}
    head = re.search(heads[prover] + local_name + r"(?![\w'-])", before, re.M | re.I)
    if head is None:
        raise ValueError("declaration locator does not bind the named target before its proof slot")
    tail = before[head.end():]
    # The proof slot must be inside the declaration that the target names.
    # Reject locators that span the end of that declaration and edit a later one.
    boundary = {
        "lean4": r"^\s*(?:#|(?:theorem|lemma|def|axiom|namespace|section|end)\b)",
        "rocq": r"\b(?:Qed|Defined|Admitted|Abort)\s*\.",
        "isabelle": r"^\s*(?:lemma|theorem|definition|end|qed|oops|sorry)\b",
        "hol-light": r";;",
        "hol4": r";|^\s*val\s+",
        "acl2": r"^\s*\(\s*(?:defthm|defun|defaxiom|value-triple|assert-event)\b",
        "agda": r"^\s*[\w-]+\s*:",
        "metamath": r"\$\.",
        "mizar": r"\bend\s*;",
        "pvs": r"^\s*%\|-\s*QED\b|^\s*[\w?-]+\s*:\s*(?:LEMMA|THEOREM)\b",
    }
    if re.search(boundary[prover], tail, re.M | re.I):
        raise ValueError("proof locator crosses the end of its named declaration")
    if prover not in {"lean4", "rocq", "hol-light", "hol4"}:
        declared = _declared_statement(prover, tail, local_name)
        expected = m.statement.strip()
        # Isabelle commonly quotes a proposition in the source declaration.
        if prover == "isabelle" and declared == '"' + expected + '"':
            declared = expected
        if declared != expected:
            raise ValueError("manifest statement disagrees with the fixed source declaration")
    # Require a proof-bearing declaration. Metamath labels, PVS formulas and
    # Agda signatures can also denote statement-only material.
    if prover == "metamath" and not re.search(local_name + r"\s+\$p\s+", before):
        raise ValueError("expected a Metamath $p target")
    if prover == "pvs" and not re.search(local_name + r"\s*:\s*(?:LEMMA|THEOREM)\b", before, re.I):
        raise ValueError("expected a PVS proof-bearing formula")
    if prover == "mizar" and "::$P-" in source.decode():
        raise ValueError("proof suppression in Mizar task")
    return source.index(anchor) + anchor.index(proof), len(proof)


def build_task(prepared, manifest_path: str = "completion.json") -> TaskSpec:
    """Load a manifest from the prepared project and bind its fixed bytes to a task."""
    task, _ = _build_with_document_template(prepared, manifest_path)
    return task


def _build_with_document_template(prepared, manifest_path: str) -> tuple[TaskSpec, bytes]:
    if getattr(prepared, "adapter", None) is not None:
        from itpeval.backends.external import build_detached_task
        return build_detached_task(prepared, manifest_path)
    m = CompletionManifest.from_dict(json.loads(
        project_file(prepared.project, manifest_path).read_text(encoding="utf-8")))
    files = {name: project_file(prepared.project, name).read_bytes() for name in m.files}
    if m.entrypoint not in files:
        raise ValueError("entrypoint must be included in the manifest")
    source = files[m.entrypoint]
    prover = prepared.spec.prover
    if prover != "pvs" and set(m.obligations) - {m.target}:
        raise ValueError(f"{prover} checks a single named target; secondary obligations require a native witness")
    start, size = _locate(m, source, prover)
    document_template = source[:start] + source[start + size:]
    probe, receipt = _observer(prover, m)
    transforms = [f"removed reference proof bytes [{start},{start + size}) of {m.entrypoint}"]
    if probe:
        anchor = (m.observer_anchor or m.anchor).encode()
        if not anchor or source.count(anchor) != 1:
            raise ValueError("ambiguous observer location")
        at = source.index(anchor) + len(anchor)
        if at < start + size:
            raise ValueError("target observer must follow the proof slot")
        source = source[:at] + b"\n" + probe.encode() + b"\n" + source[at:]
        transforms.append(f"inserted native target observer after source byte {at}")
    files[m.entrypoint] = source[:start] + source[start + size:]
    artifact = Artifact.from_files(m.entrypoint, files, tuple(transforms))
    task = TaskSpec(prover, prepared.environment_id, "proof_completion", artifact, targets=(m.target,),
                    editable_regions=(EditableRegion(m.entrypoint, start, start),),
                    allowed_assumptions=m.allowed_assumptions, allowed_edits=m.allowed_edits,
                    obligations=tuple(dict.fromkeys((m.target, *m.obligations))),
                    manifest_path=manifest_path, proof_atoms=m.proof_atoms, native_receipt=receipt,
                    budgets=m.budgets, dependency_sources=m.dependency_sources)
    return task, document_template
