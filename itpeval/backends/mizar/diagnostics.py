"""Native Mizar proof theses and structured article diagnostics."""
from __future__ import annotations

from dataclasses import dataclass
import os
from pathlib import Path
import re
from tempfile import TemporaryDirectory
from time import monotonic
import xml.etree.ElementTree as ET

from itpeval.core.records import Record
from itpeval.core.types import Artifact
from itpeval.corpus.storage import digest
from itpeval.runtime.process import run_process
from itpeval.verification.policies import assemble, reviewed_document_template, validate_inputs


def article_errors(task, evidence):
    """Return source coordinates and Mizar error numbers for this exact task."""
    if (task.prover != "mizar" or evidence.task_id != task.task_id or
            evidence.environment_id != task.environment_id):
        raise ValueError("Mizar diagnostics require evidence for the same task and environment")
    prefix = r"^\[ITPEval\]\s+line (\d+), column (\d+), error (\d+)\s*$"
    return tuple({"path": task.artifact.entrypoint, "line": int(line), "column": int(column),
                  "error_code": int(code)} for line, column, code in re.findall(prefix, evidence.stderr, re.M))


@dataclass(frozen=True)
class MizarDiagnostic(Record):
    line: int
    column: int
    error_code: int
    message: str | None


@dataclass(frozen=True)
class MizarThesis(Record):
    kind: str
    xml_path: tuple[int, ...]
    formula_kind: str
    formula_xml: str


@dataclass(frozen=True)
class MizarProofTrace(Record):
    task_id: str
    environment_id: str
    source_path: str
    source_sha256: str
    target: str
    article_checked: bool
    theses: tuple[MizarThesis, ...]
    diagnostics: tuple[MizarDiagnostic, ...]
    target_line: int | None = None
    target_column: int | None = None
    stdout: str = ""
    stderr: str = ""


class _TraceError(RuntimeError):
    def __init__(self, outcome, message):
        super().__init__(message)
        self.outcome = outcome


def _mizar_messages(library):
    path = library / "mizar.msg"
    if not path.is_file():
        return {}
    return {int(number): text.strip() for number, text in re.findall(
        r"^#\s*(\d+)[ \t]*\n(.*?)(?=^#|\Z)", path.read_text(encoding="latin-1"), re.M | re.S)}


def _theses(proof, path=()):
    for index, node in enumerate(proof):
        here = (*path, index)
        if node.tag in {"Thesis", "BlockThesis"}:
            formula = node[0]
            yield MizarThesis(node.tag, here, formula.tag, ET.tostring(formula, encoding="unicode").strip())
        else:
            yield from _theses(node, here)


def _target_theorem(article, syntax, target):
    items = {(row.get("line"), row.get("col")): row for row in syntax.findall("Item")}
    matches = []
    for index, theorem in enumerate(article.findall("JustifiedTheorem"), 1):
        location = (theorem.get("line"), theorem.get("col"))
        item = items.get(location)
        label = item.find("Proposition/Label") if item is not None else None
        # Mirror the extractor's theorem numbering for an absent explicit label.
        name = label.get("spelling") if label is not None else None
        if (name or f"Th{index}").casefold() == target.casefold():
            matches.append(theorem)
    return matches[0] if len(matches) == 1 else None


def _reviewed_template(task, prepared):
    if (task.prover != "mizar" or prepared.spec.prover != "mizar" or task.operation != "proof_completion"
            or prepared.spec.checking_profile != "strict" or task.environment_id != prepared.environment_id):
        raise ValueError("expected a reviewed Mizar proof task in its prepared environment")
    template = reviewed_document_template(task, prepared)
    if template is None:
        raise ValueError("expected a reviewed Mizar proof task in its prepared environment")
    return template


def _article_revision(task, candidate):
    if candidate is None or candidate == "":
        return task.artifact
    if not isinstance(candidate, str):
        raise ValueError("a Mizar proof fragment must be text")
    if candidate.strip():
        return assemble(task, candidate)
    # Keep the submitted whitespace in an open slot so native positions still
    # refer to the actual revision. It cannot contribute a proof command.
    region, = task.editable_regions
    files = {file.path: file.data for file in task.artifact.files}
    source = files[region.path]
    files[region.path] = source[:region.start] + candidate.encode("utf-8") + source[region.end:]
    return Artifact.from_files(task.artifact.entrypoint, files, task.artifact.transformations)


def proof_trace(task, candidate, *, prepared, cancel=None) -> MizarProofTrace:
    """Read native XML thesis progression for a reviewed fragment or open slot."""
    _reviewed_template(task, prepared)
    return _trace_article(task, _article_revision(task, candidate), prepared, cancel=cancel)


def _trace_article(task, artifact, prepared, *, cancel=None):
    prepared.validate()
    validate_inputs(task, artifact)
    entry = Path(artifact.entrypoint)
    if entry.suffix != ".miz":
        raise ValueError("expected the proof task's Mizar article")
    source = next(file.data for file in artifact.files if file.path == artifact.entrypoint)
    tool = prepared.prefix / "mizar/bin"
    library = dict(prepared.library_paths).get("mizfiles")
    env = {k: os.environ[k] for k in ("HOME", "PATH", "USER", "LANG", "LC_ALL") if k in os.environ}
    env.update(prepared.environment)
    if library is None:
        library = prepared.prefix / "mizar/vendor/mizfiles"
    else:
        tool = prepared.prefix / "mizar/vendor/bin"
        env.update(MIZFILES=str(library), PATH=str(tool) + os.pathsep + env.get("PATH", ""))
    budgets = task.budgets
    deadline = monotonic() + budgets.timeout_s

    def native(command, root):
        remaining = deadline - monotonic()
        if remaining <= 0:
            raise _TraceError("timeout", "Mizar proof trace exhausted the wall-time budget")
        check = run_process([str(part) for part in command], cwd=root, env=env, cancel=cancel,
                            timeout_s=remaining, max_log_bytes=budgets.max_log_bytes,
                            cpu_seconds=budgets.cpu_seconds, memory_bytes=budgets.memory_bytes)
        if check.outcome != "exited" or check.truncated:
            raise _TraceError(check.outcome, f"Mizar proof trace failed ({check.outcome}): "
                                             f"{(check.stdout + check.stderr)[-1600:]}")
        return check

    with TemporaryDirectory(prefix="itpeval-mizar-thesis-") as temp:
        root = Path(temp)
        artifact.materialize(root)
        stem = entry.with_suffix("")
        paths = {suffix: root / entry.with_suffix(suffix) for suffix in (".xml", ".wsx", ".err")}
        for file in paths.values():
            file.unlink(missing_ok=True)
        accommodation = native([tool / "makeenv", stem], root)
        if accommodation.returncode:
            raise ValueError(f"Mizar could not accommodate the locked article: {accommodation.stdout[-1600:]}")
        verifier = native([tool / "verifier", "-x", stem], root)
        errors = paths[".err"]
        if not errors.is_file() or errors.stat().st_size > budgets.max_log_bytes:
            raise ValueError("Mizar did not return article diagnostics within the output budget")
        messages = _mizar_messages(library)
        diagnostics = []
        for line in errors.read_text(encoding="ascii").splitlines():
            if line.strip():
                row, col, code, *_ = map(int, line.split())
                diagnostics.append(MizarDiagnostic(row, col, code, messages.get(code)))
        theses = ()
        target_line = target_column = None
        if paths[".xml"].is_file() and paths[".wsx"].is_file():
            if any(file.stat().st_size > budgets.max_log_bytes for file in paths.values()):
                raise ValueError("Mizar native XML exceeds the task's output budget")
            try:
                theorem = _target_theorem(ET.parse(paths[".xml"]).getroot(), ET.parse(paths[".wsx"]).getroot(),
                                          task.targets[0])
            except ET.ParseError as exc:
                if not diagnostics:
                    raise ValueError("Mizar did not return readable proof XML") from exc
                theorem = None
            if theorem is not None:
                target_line, target_column = (int(theorem.attrib[key]) if key in theorem.attrib else None
                                              for key in ("line", "col"))
                proof = theorem.find("Proof")
                if proof is not None:
                    theses = tuple(_theses(proof))
                else:
                    proposition = theorem.find("Proposition")
                    if proposition is not None and len(proposition):
                        formula = proposition[0]
                        theses = (MizarThesis("Proposition", (list(theorem).index(proposition),), formula.tag,
                                             ET.tostring(formula, encoding="unicode").strip()),)
            elif not diagnostics:
                raise ValueError("Mizar did not emit one occurrence of the named theorem")
        elif not diagnostics:
            raise ValueError("Mizar did not emit proof XML or article errors")
    return MizarProofTrace(task.task_id, task.environment_id, artifact.entrypoint, digest(source), task.targets[0],
                           verifier.returncode == 0 and not diagnostics, theses, tuple(diagnostics),
                           target_line, target_column, accommodation.stdout + verifier.stdout,
                           accommodation.stderr + verifier.stderr)
