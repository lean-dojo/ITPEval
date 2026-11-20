"""Run a local automated theorem prover and preserve its native result."""

from __future__ import annotations

import os
import re
import shutil
from dataclasses import dataclass
from pathlib import Path
from tempfile import TemporaryDirectory
from threading import Event

from itpeval.core.records import Record, digest
from itpeval.core.types import Budgets
from itpeval.environments.cache import sha256
from itpeval.runtime.process import ProcessResult, run_process

from .tptp import stage_problem


_SOLVERS = {
    "e": ("eprover", "E_HOME", ("--auto", "--tstp-format", "--proof-object")),
    "vampire": ("vampire", "VAMPIRE_HOME", ("--input_syntax", "tptp", "--proof", "tptp")),
}
SOLVERS = tuple(_SOLVERS)
_SZS_STATUS = re.compile(r"^\s*[%#]\s*SZS status\s+(\w+)\b", re.MULTILINE)
_SZS_DATA = re.compile(
    r"^\s*[%#](?:\s*#)?\s*SZS output (start|end) (\w+)\b[^\r\n]*",
    re.MULTILINE,
)
_LOGICAL_OUTCOMES = {
    "Theorem": "theorem",
    "SatisfiableAxiomsTheorem": "theorem",
    "Unsatisfiable": "unsatisfiable",
    "CounterSatisfiable": "counter_satisfiable",
    "Satisfiable": "satisfiable",
    "ContradictoryAxioms": "contradictory_axioms",
}
_FAILURES = {
    "Timeout": "timeout",
    "ResourceOut": "resource_exhausted",
    "MemoryOut": "resource_exhausted",
    "Error": "solver_error",
    "InputError": "solver_error",
    "SyntaxError": "solver_error",
    "TypeError": "solver_error",
    "Inappropriate": "unsupported",
    "GaveUp": "unknown",
    "Incomplete": "unknown",
    "Unknown": "unknown",
}


@dataclass(frozen=True)
class SolverBuild(Record):
    solver: str
    version: str
    executable_sha256: str


@dataclass(frozen=True)
class SolverProcess(Record):
    execution_outcome: str
    returncode: int
    duration_ms: int
    stdout: str
    stderr: str
    logs_truncated: bool
    peak_process_rss_bytes: int | None
    cpu_time_s: float | None

    @classmethod
    def from_process(cls, result: ProcessResult) -> SolverProcess:
        return cls(result.outcome, result.returncode, result.duration_ms, result.stdout, result.stderr,
                   result.truncated, result.peak_process_rss_bytes, result.cpu_time_s)


@dataclass(frozen=True)
class SearchEvidence(Record):
    solver: SolverBuild
    problem_id: str
    entrypoint: str
    inputs: tuple[tuple[str, str, str, str], ...]
    arguments: tuple[str, ...]
    budgets: Budgets
    process: SolverProcess
    native_status: str | None
    outcome: str
    certificate_kind: str | None
    certificate: str | None

    @property
    def conclusive(self) -> bool:
        return self.outcome in _LOGICAL_OUTCOMES.values()


@dataclass(frozen=True)
class PreparedSolver:
    """Reuse a fingerprinted local solver across independently staged problems."""

    executable: Path
    build: SolverBuild

    def solve(self, problem: Path, *, tptp_root: Path | None = None, budgets: Budgets | None = None,
              cancel: Event | None = None) -> SearchEvidence:
        budgets = budgets or Budgets(timeout_s=30)
        binary, solver = self.executable, self.build.solver
        if sha256(binary) != self.build.executable_sha256:
            raise ValueError("automated prover executable differs from its prepared build")
        with TemporaryDirectory(prefix="itpeval-atp-") as temp:
            workspace = Path(temp)
            home = workspace / "home"
            home.mkdir()
            entrypoint, staged, files = stage_problem(problem, tptp_root, workspace)
            arguments = (*_SOLVERS[solver][2], staged)
            result = run_process([str(binary), *arguments], cwd=workspace,
                                 env={**native_environment(home), "TPTP": str(workspace)},
                                 timeout_s=budgets.timeout_s, max_log_bytes=budgets.max_log_bytes,
                                 memory_bytes=budgets.memory_bytes, cpu_seconds=budgets.cpu_seconds,
                                 cancel=cancel)
            if sha256(binary) != self.build.executable_sha256:
                raise ValueError("automated prover executable changed during proof search")
        status, outcome, certificate_kind, certificate = _parse_search(solver, result)
        problem_id = digest([entrypoint, [(path, content) for path, content, _, _ in files]])
        return SearchEvidence(self.build, problem_id, entrypoint, files, arguments, budgets,
                              SolverProcess.from_process(result), status, outcome, certificate_kind, certificate)


def native_environment(home: Path) -> dict[str, str]:
    values = {k: os.environ[k] for k in ("PATH", "USER", "LOGNAME") if k in os.environ}
    return {**values, "HOME": str(home), "USER_HOME": str(home), "LC_ALL": "C.UTF-8"}


def _isabelle_component(solver: str, isabelle: Path, home: Path) -> Path:
    name, variable, _ = _SOLVERS[solver]
    result = run_process([str(isabelle), "getenv", "-b", variable], env=native_environment(home),
                         timeout_s=10, max_log_bytes=8192)
    directory = Path(result.stdout.strip())
    if result.outcome != "exited" or result.returncode or result.truncated or not directory.is_absolute():
        raise ValueError(f"Isabelle did not locate its local {solver} component")
    return directory / name


def _executable(solver, provided, prefix, home):
    if solver not in _SOLVERS:
        raise ValueError(f"unknown automated prover: {solver!r}")
    name, _, _ = _SOLVERS[solver]
    if provided is not None:
        choices = [Path(provided)]
    else:
        path = shutil.which(name)
        choices = [Path(path)] if path is not None else []
        if prefix is None:
            from itpeval.cli.lib import default_prefix

            prefix = default_prefix()
        root = Path(prefix).expanduser().resolve()
        choices.append(root / "atp" / solver / "bin" / name)
        if not any(path.is_file() and os.access(path, os.X_OK) for path in choices):
            isabelle = root / "isabelle/bin/isabelle"
            if isabelle.is_file() and os.access(isabelle, os.X_OK):
                choices.append(_isabelle_component(solver, isabelle, home))
    for path in choices:
        resolved = path.expanduser().resolve()
        if resolved.is_file() and os.access(resolved, os.X_OK):
            return resolved
    raise FileNotFoundError(f"could not find {name}; pass an executable or install its Isabelle component")


def _fingerprint(solver: str, binary: Path, home: Path) -> SolverBuild:
    build_hash = sha256(binary)
    query = run_process([str(binary), "--version"], cwd=home, env=native_environment(home),
                        timeout_s=10, max_log_bytes=8192)
    version = (query.stdout or query.stderr).strip()
    if query.outcome != "exited" or query.returncode or query.truncated or not version:
        raise ValueError(f"could not identify the local {solver} build")
    if sha256(binary) != build_hash:
        raise ValueError("automated prover executable changed during version probing")
    return SolverBuild(solver, version, build_hash)


def prepare_solver(solver: str = "e", *, executable: Path | None = None, prefix: Path | None = None) -> PreparedSolver:
    """Discover the local executable and record its version and contents once."""
    with TemporaryDirectory(prefix="itpeval-atp-discovery-") as temp:
        home = Path(temp)
        binary = _executable(solver, executable, prefix, home)
        return PreparedSolver(binary, _fingerprint(solver, binary, home))


def _parse_search(solver, result):
    statuses = set(_SZS_STATUS.findall(result.stdout + "\n" + result.stderr))
    status = next(iter(statuses)) if len(statuses) == 1 else None
    if result.outcome != "exited":
        return status, result.outcome, None, None
    if result.truncated:
        return status, "output_truncated", None, None
    if len(statuses) > 1:
        return None, "protocol_error", None, None
    # E uses exit code 1 for a completed saturation without refutation.
    saturation = solver == "e" and status in ("Satisfiable", "CounterSatisfiable")
    if status is None or (result.returncode and not (saturation and result.returncode == 1)):
        return status, _FAILURES.get(status, "solver_error"), None, None
    outcome = _LOGICAL_OUTCOMES.get(status, _FAILURES.get(status, "unknown"))
    start = None
    for match in _SZS_DATA.finditer(result.stdout):
        direction, kind = match.groups()
        if direction == "start":
            start = match
        elif start is not None and start.group(2) == kind:
            payload = result.stdout[start.end():match.start()].strip()
            if payload:
                return status, outcome, kind, payload
            start = None
    return status, outcome, None, None


def solve_tptp(problem: Path, *, solver: str = "e", executable: Path | None = None,
               prefix: Path | None = None, tptp_root: Path | None = None,
               budgets: Budgets | None = None, cancel: Event | None = None) -> SearchEvidence:
    """Ask E or Vampire to solve a native TPTP problem in a private directory.

    A final SZS status is a solver report. Users can validate the emitted
    certificate independently or replay a corresponding proof in an ITP.
    """
    prepared = prepare_solver(solver, executable=executable, prefix=prefix)
    return prepared.solve(problem, tptp_root=tptp_root, budgets=budgets, cancel=cancel)
