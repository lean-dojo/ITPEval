#!/usr/bin/env python3
from __future__ import annotations

import argparse
import os
import subprocess
import sys
import tempfile
from dataclasses import dataclass
from pathlib import Path
from typing import TYPE_CHECKING


if __package__ in (None, ""):  # Support python itpeval/itp.py from a checkout.
    sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

from itpeval.adapter_paths import adapter_root
from itpeval.staging import (
    HOL4_TARGET_MARKER as HOL4_TARGET_MARKER,
    hol4_wrapper_text as hol4_wrapper_text,
    prepare_task_dir as _prepare_task_dir,
)
from itpeval.core.types import Budgets, TaskSpec, VerificationEvidence
from itpeval.runtime.checker import execute_checker
from itpeval.runtime.process import run_process, task_environment

if TYPE_CHECKING:
    from itpeval.environments import PreparedProject


@dataclass(frozen=True)
class RunResult:
    """Outcome and bounded native diagnostics for a file or snippet check."""

    prover: str
    ok: bool
    returncode: int
    duration_ms: int
    command: list[str]
    workdir: Path
    stdout: str
    stderr: str
    execution_outcome: str = "exited"
    peak_process_rss_bytes: int | None = None
    cpu_time_s: float | None = None
    logs_truncated: bool = False


def _itpeval_root() -> Path:
    return Path(__file__).resolve().parent


def _default_prefix() -> Path:
    root = _itpeval_root()
    env_prefix = os.environ.get("ITPEVAL_PREFIX")
    if env_prefix:
        return Path(env_prefix).expanduser().resolve()
    if str(root).startswith("/efs/"):
        return Path("/tmp/itpeval-toolchains").resolve()
    installed = Path(os.environ.get("XDG_DATA_HOME", Path.home() / ".local/share")) / "itpeval/toolchains"
    # A versioned deployment can atomically select a qualified toolchain set.
    current = installed / "current"
    if current.is_dir():
        return current.resolve()
    if (root.parent / "pyproject.toml").is_file():
        return (root / "_toolchains").resolve()
    return installed


def _check_script(prover: str) -> Path:
    return adapter_root(prover) / "check.sh"


def _install_script(prover: str) -> Path:
    return adapter_root(prover) / "install.sh"


def run_itp(
    *,
    prover: str | None = None,
    code: str | None = None,
    code_path: Path | None = None,
    task_dir: Path | None = None,
    task_file: Path | None = None,
    mode: str = "raw",
    prefix: Path | None = None,
    timeout_s: int | None = None,
    ensure_installed: bool = False,
    install_timeout_s: int | None = None,
    budgets: Budgets | None = None,
    install_budgets: Budgets | None = None,
    cancel=None,
    task: TaskSpec | None = None,
    candidate: str | None = None,
    prepared: PreparedProject | None = None,
    retain_dir: Path | None = None,
) -> RunResult | VerificationEvidence:
    """Run a locked task or a historical file, snippet or staged directory.

    The task form returns the verifier's full evidence. Its lock and TaskSpec
    supply the prover, operation and budgets. Legacy calls keep their original
    RunResult, staging conventions and timeout behavior.
    """
    if task is not None:
        if prepared is None or prover not in (None, task.prover):
            raise ValueError("a typed task requires its matching prover and prepared project")
        if (any(v is not None for v in (code, code_path, task_dir, task_file, prefix, timeout_s,
                                        install_timeout_s, budgets, install_budgets))
                or mode != "raw" or ensure_installed):
            raise ValueError("a typed task supplies its own artifact, toolchain and budgets")
        from itpeval.verification.service import verify
        return verify(task, candidate, prepared=prepared, cancel=cancel, retain_dir=retain_dir)
    if candidate is not None or prepared is not None or retain_dir is not None:
        raise ValueError("candidate, prepared and retain_dir require a typed task")
    if prover is None:
        raise TypeError("run_itp requires a prover or a typed task")
    if task_file is not None and task_dir is None:
        raise ValueError("--task-file requires --task-dir")

    if prefix is None:
        prefix = _default_prefix()
    prefix = prefix.expanduser().resolve()

    script = _check_script(prover)
    if not script.exists():
        raise FileNotFoundError(f"missing check script: {script}")

    prepared_task_file: Path | None = None
    if task_dir is not None:
        workdir = task_dir.expanduser().resolve()
        if not workdir.is_dir():
            raise FileNotFoundError(f"--task-dir is not a directory: {workdir}")
    else:
        if code_path is not None:
            if code is not None:
                raise ValueError("pass only one of code/code_path")
            code = Path(code_path).expanduser().read_text(encoding="utf-8")
        if code is None:
            raise ValueError("provide either code/code_path or --task-dir")
        tmp_root = Path(tempfile.mkdtemp(prefix=f"itpeval-{prover}-"))
        workdir = tmp_root
        prepared_task_file = _prepare_task_dir(
            prover=prover,
            code=code,
            mode=mode,
            task_dir=workdir,
        )

    env = task_environment()
    env["ITPEVAL_OPERATION"] = "legacy"
    env["ITPEVAL_PYTHON"] = sys.executable
    env["ITPEVAL_PREFIX"] = str(prefix)
    env["ITPEVAL_TASK_DIR"] = str(workdir)
    selected_task_file = task_file or prepared_task_file
    if selected_task_file is not None:
        candidate = selected_task_file.expanduser()
        if not candidate.is_absolute():
            candidate = workdir / candidate
        candidate = candidate.resolve()
        try:
            relative_task_file = candidate.relative_to(workdir)
        except ValueError as exc:
            raise ValueError(
                f"task file must be inside task directory: {candidate}"
            ) from exc
        if not candidate.is_file():
            raise FileNotFoundError(f"task file does not exist: {candidate}")
        env["ITPEVAL_TASK_FILE"] = relative_task_file.as_posix()

    if ensure_installed:
        install_script = _install_script(prover)
        if not install_script.exists():
            raise FileNotFoundError(f"missing install script: {install_script}")
        install_env = env.copy()
        install_env.pop("ITPEVAL_TASK_DIR", None)
        install_env.pop("ITPEVAL_TASK_FILE", None)
        install_log = workdir / ".itpeval.install.log"
        install_limits = install_budgets or Budgets()
        if install_timeout_s is None and install_budgets is not None:
            install_timeout_s = install_budgets.timeout_s
        completed_install = run_process(["/bin/bash", str(install_script)], env=install_env,
                                        cwd=_itpeval_root(), timeout_s=install_timeout_s,
                                        merge_stderr=True, cancel=cancel, cpu_seconds=install_limits.cpu_seconds,
                                        memory_bytes=install_limits.memory_bytes,
                                        max_log_bytes=install_limits.max_log_bytes)
        install_log.write_text(completed_install.stdout, encoding="utf-8")
        if completed_install.returncode != 0:
            try:
                tail = install_log.read_text(encoding="utf-8", errors="replace").splitlines()[-200:]
                tail_text = "\n".join(tail).rstrip()
            except Exception:
                tail_text = "<unable to read install log>"
            raise RuntimeError(
                "\n".join(
                    [
                        f"install failed for prover={prover} rc={completed_install.returncode}",
                        f"install_log={install_log}",
                        "--- last 200 lines ---",
                        tail_text,
                    ]
                ).rstrip()
            )

    command = ["/bin/bash", str(script)]
    limits = budgets or Budgets()
    if timeout_s is None and budgets is not None:
        timeout_s = budgets.timeout_s
    completed = execute_checker(script, workdir, env, timeout_s=timeout_s, cancel=cancel,
                                memory_bytes=limits.memory_bytes, cpu_seconds=limits.cpu_seconds,
                                max_log_bytes=limits.max_log_bytes)
    if completed.outcome == "timeout":
        raise subprocess.TimeoutExpired(command, timeout_s, completed.stdout, completed.stderr)
    duration_ms = completed.duration_ms
    ok = completed.outcome == "exited" and completed.returncode == 0
    return RunResult(
        prover=prover,
        ok=ok,
        returncode=int(completed.returncode),
        duration_ms=duration_ms,
        command=["/bin/bash", str(script)],
        workdir=workdir,
        stdout=completed.stdout,
        stderr=completed.stderr, execution_outcome=completed.outcome,
        peak_process_rss_bytes=completed.peak_process_rss_bytes, cpu_time_s=completed.cpu_time_s,
        logs_truncated=completed.truncated,
    )


def _build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(
        prog="itp.py",
        description="One-file unified runner for ITPEval prover adapters.",
    )
    parser.add_argument("--prover", required=True, help="prover name (e.g. lean4, rocq, isabelle, agda)")
    parser.add_argument(
        "--mode",
        default="raw",
        choices=("raw", "snippet"),
        help="how to interpret --code/--file (default: raw)",
    )
    parser.add_argument("--prefix", default=None, help="toolchain prefix (defaults to ITPEVAL_PREFIX or itpeval/_toolchains)")
    parser.add_argument("--timeout-s", type=int, default=None, help="timeout in seconds")
    parser.add_argument(
        "--ensure-installed",
        action="store_true",
        help="run the prover's install.sh before checking (useful for one-file usage)",
    )

    source = parser.add_mutually_exclusive_group(required=True)
    source.add_argument("--code", default=None, help="inline code (file contents or snippet)")
    source.add_argument("--file", default=None, help="path to a code file to run")
    source.add_argument("--task-dir", default=None, help="pre-built task directory to run (must match prover's check.sh expectations)")
    parser.add_argument(
        "--task-file",
        default=None,
        help="file inside --task-dir selected for adapters that support task-file overrides",
    )
    return parser


def main(argv: list[str] | None = None) -> int:
    args = _build_parser().parse_args(argv)
    prefix = Path(args.prefix).expanduser().resolve() if args.prefix else None
    code_path = Path(args.file) if args.file else None
    task_dir = Path(args.task_dir) if args.task_dir else None
    task_file = Path(args.task_file) if args.task_file else None
    try:
        result = run_itp(
            prover=args.prover,
            code=args.code,
            code_path=code_path,
            task_dir=task_dir,
            task_file=task_file,
            mode=args.mode,
            prefix=prefix,
            timeout_s=args.timeout_s,
            ensure_installed=bool(args.ensure_installed),
        )
    except subprocess.TimeoutExpired as exc:
        print(f"[ITPEval] TIMEOUT after {args.timeout_s}s: {exc}", file=sys.stderr)
        return 2
    except Exception as exc:
        print(f"[ITPEval] ERROR: {exc}", file=sys.stderr)
        return 2

    stream = sys.stdout if result.ok else sys.stderr
    print(f"[ITPEval] prover={result.prover} ok={result.ok} rc={result.returncode} ms={result.duration_ms}", file=stream)
    if result.stdout.strip():
        print("--- stdout ---", file=stream)
        print(result.stdout.rstrip(), file=stream)
    if result.stderr.strip():
        print("--- stderr ---", file=stream)
        print(result.stderr.rstrip(), file=stream)
    print(f"[ITPEval] workdir={result.workdir}", file=stream)
    return 0 if result.ok else 1


if __name__ == "__main__":
    raise SystemExit(main())
