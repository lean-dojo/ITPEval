#!/usr/bin/env python3
from __future__ import annotations

import argparse
import os
import re
import subprocess
import sys
import tempfile
import time
from dataclasses import dataclass
from pathlib import Path


@dataclass(frozen=True)
class RunResult:
    prover: str
    ok: bool
    returncode: int
    duration_ms: int
    command: list[str]
    workdir: Path
    stdout: str
    stderr: str


def _itpeval_root() -> Path:
    return Path(__file__).resolve().parent


def _default_prefix() -> Path:
    root = _itpeval_root()
    env_prefix = os.environ.get("ITPEVAL_PREFIX")
    if env_prefix:
        return Path(env_prefix).expanduser().resolve()
    if str(root).startswith("/efs/"):
        return Path("/tmp/itpeval-toolchains").resolve()
    return (root / "_toolchains").resolve()


def _check_script(prover: str) -> Path:
    return _adapter_dir(prover) / "check.sh"

def _install_script(prover: str) -> Path:
    return _adapter_dir(prover) / "install.sh"


HOL4_TARGET_MARKER = "(* ITPEVAL_AGENT_TARGET *)"


def hol4_wrapper_text() -> str:
    return "\n".join(
        (
            "open HolKernel Parse boolLib;",
            "",
            'val _ = new_theory "hello";',
            "",
            HOL4_TARGET_MARKER,
            "",
            "val _ = export_theory();",
            "",
        )
    )


def _adapter_dir(prover: str) -> Path:
    """Return the native adapter directory for a prover."""
    return _itpeval_root() / "provers" / prover


def _write_text(path: Path, content: str) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(content if content.endswith("\n") else content + "\n", encoding="utf-8")


def _uncomment_isabelle(code: str) -> str:
    uncommented: list[str] = []
    depth = 0
    index = 0
    while index < len(code):
        if code.startswith("(*", index):
            depth += 1
            uncommented.extend("  ")
            index += 2
            continue
        if depth and code.startswith("*)", index):
            depth -= 1
            uncommented.extend("  ")
            index += 2
            continue

        char = code[index]
        uncommented.append(char if depth == 0 or char == "\n" else " ")
        index += 1

    return "".join(uncommented)


def _isabelle_theory_name(code: str) -> str:
    match = re.search(
        r'(?m)^\s*theory\s+"?([A-Za-z][A-Za-z0-9_\'.-]*)"?\b',
        _uncomment_isabelle(code),
    )
    return match.group(1) if match else "Hello"


def _isabelle_session_imports(code: str) -> list[str]:
    header = re.search(
        r"(?ms)^\s*theory\b.*?\bimports\b(?P<imports>.*?)^\s*begin\b",
        _uncomment_isabelle(code),
    )
    if header is None:
        return []

    sessions = {
        theory_name.split(".", maxsplit=1)[0]
        for theory_name in re.findall(r'"([^"]+)"', header.group("imports"))
        if "." in theory_name and theory_name.split(".", maxsplit=1)[0].startswith("HOL-")
    }
    return sorted(sessions)


def _normalize_isabelle_placeholders(code: str) -> str:
    return re.sub(r"(?m)^([ \t]*)by[ \t]+sorry[ \t]*$", r"\1sorry", code)


def _agda_module_name(code: str) -> str:
    uncommented = re.sub(r"(?m)--.*$", "", code)
    match = re.search(
        r"(?m)^\s*module\s+([^\s;]+)\s+where\b",
        uncommented,
    )
    return match.group(1) if match else "Hello"


def _agda_module_path(module_name: str) -> Path:
    parts = module_name.split(".")
    if any(
        not part
        or part in {".", ".."}
        or "/" in part
        or "\\" in part
        for part in parts
    ):
        raise ValueError(f"unsafe Agda module name: {module_name!r}")
    return Path(*parts[:-1], f"{parts[-1]}.agda")


def _pvs_theory_name(code: str) -> str:
    uncommented = re.sub(r"(?m)%.*$", "", code)
    match = re.search(
        r"(?im)^\s*([A-Za-z][A-Za-z0-9_?'-]*)"
        r"(?:\s*\[[^\n]*\])?\s*:\s*THEORY\b",
        uncommented,
    )
    return match.group(1) if match else "Hello"


def _prepare_task_dir(
    *,
    prover: str,
    code: str,
    mode: str,
    task_dir: Path,
) -> Path | None:
    """
    Creates the minimal file layout expected by the selected prover adapter.

    mode:
      - raw: `code` is treated as the full file contents (except where a wrapper is mandatory).
      - snippet: `code` is inserted into a small skeleton (only where a wrapper is mandatory).
    """
    mode = mode.lower().strip()
    if mode not in {"raw", "snippet"}:
        raise ValueError(f"unknown mode: {mode!r}")

    if prover == "lean4":
        _write_text(task_dir / "Hello.lean", code)
        return None

    if prover == "rocq":
        _write_text(task_dir / "hello.v", code)
        return None

    if prover == "agda":
        if mode == "snippet":
            wrapped = "module Hello where\n\n" + code
            relative = Path("Hello.agda")
            _write_text(task_dir / relative, wrapped)
        else:
            relative = _agda_module_path(_agda_module_name(code))
            _write_text(task_dir / relative, code)
        return relative

    if prover == "isabelle":
        if mode == "snippet":
            theory_name = "Hello"
            session_name = "ITPEval_Hello"
            thy = "theory Hello\n  imports Main\nbegin\n\n" + code + "\n\nend\n"
        else:
            theory_name = _isabelle_theory_name(code)
            session_name = f"ITPEval_{theory_name}"
            thy = _normalize_isabelle_placeholders(code)

        root_lines = [f'session "{session_name}" = HOL +']
        session_imports = _isabelle_session_imports(thy)
        if session_imports:
            root_lines.append("  sessions")
            root_lines.extend(f'    "{session}"' for session in session_imports)
        root_lines.extend(("  theories", f"    {theory_name}"))
        _write_text(
            task_dir / "ROOT",
            "\n".join(root_lines),
        )
        _write_text(task_dir / f"{theory_name}.thy", thy)
        return None

    if prover == "hol-light":
        _write_text(task_dir / "hello.ml", code)
        return None

    if prover == "hol4":
        target = Path("AgentTarget.sml")
        _write_text(task_dir / target, code)
        _write_text(task_dir / "Holmakefile", "THEORIES = hello")
        _write_text(task_dir / "helloScript.sml", hol4_wrapper_text())
        return target

    if prover in {"acl2", "acl2r"}:
        _write_text(task_dir / "hello.lsp", code)
        return Path("hello.lsp")

    if prover == "metamath":
        _write_text(task_dir / "hello.mm", code)
        return Path("hello.mm")

    if prover == "mizar":
        if mode == "snippet":
            wrapped = "environ\n\nbegin\n\n" + code + "\n"
            _write_text(task_dir / "hello.miz", wrapped)
        else:
            _write_text(task_dir / "hello.miz", code)
        return Path("hello.miz")

    if prover == "pvs":
        if mode == "snippet":
            theory_name = "Hello"
            wrapped = (
                f"{theory_name}: THEORY\n"
                "BEGIN\n\n"
                f"{code}\n\n"
                f"END {theory_name}\n"
            )
        else:
            theory_name = _pvs_theory_name(code)
            wrapped = code
        target = Path(f"{theory_name}.pvs")
        _write_text(task_dir / target, wrapped)
        return target

    raise NotImplementedError(f"unsupported prover: {prover}")


def run_itp(
    *,
    prover: str,
    code: str | None = None,
    code_path: Path | None = None,
    task_dir: Path | None = None,
    task_file: Path | None = None,
    mode: str = "raw",
    prefix: Path | None = None,
    timeout_s: int | None = None,
    ensure_installed: bool = False,
) -> RunResult:
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

    env = os.environ.copy()
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
        with install_log.open("w", encoding="utf-8") as handle:
            completed_install = subprocess.run(
                ["/bin/bash", str(install_script)],
                env=install_env,
                cwd=str(_itpeval_root()),
                stdout=handle,
                stderr=subprocess.STDOUT,
                check=False,
                text=True,
            )
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

    started = time.time()
    completed = subprocess.run(
        ["/bin/bash", str(script)],
        env=env,
        cwd=str(workdir),
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        timeout=timeout_s,
        check=False,
        text=True,
    )
    duration_ms = int((time.time() - started) * 1000)
    ok = completed.returncode == 0
    return RunResult(
        prover=prover,
        ok=ok,
        returncode=int(completed.returncode),
        duration_ms=duration_ms,
        command=["/bin/bash", str(script)],
        workdir=workdir,
        stdout=completed.stdout,
        stderr=completed.stderr,
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
