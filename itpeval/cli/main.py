from __future__ import annotations

import argparse
import json
import os
import sys
from pathlib import Path
from typing import Iterable

from itpeval.atp.cli import add_commands as add_atp_commands

from . import lib
from .projects import add_commands
from .toolchains import add_commands as add_toolchain_commands


def selected_provers(args: argparse.Namespace) -> list[str]:
    if getattr(args, "provers", None):
        return list(args.provers)
    env_value = os.environ.get("ITPEVAL_PROVERS", "").strip()
    if env_value:
        return [item for item in env_value.replace(",", " ").split() if item]
    return lib.discover_provers()


def command_list_provers(args: argparse.Namespace) -> int:
    for prover in selected_provers(args):
        print(prover)
    return 0


def command_stage(args: argparse.Namespace, *, command_name: str, stages: Iterable[str]) -> int:
    prefix = Path(args.prefix).expanduser().resolve()
    task_value = getattr(args, "task", None)
    task_name = task_value if command_name in {"check", "run"} else None
    if task_name is not None and task_name.strip().lower() in {"", "none", "hello"}:
        task_name = None

    run_dir = (
        Path(args.run_dir).expanduser().resolve()
        if args.run_dir
        else lib.create_run_dir(command_name, prefix, task_name)
    )
    run_dir.mkdir(parents=True, exist_ok=True)
    (run_dir / "logs").mkdir(parents=True, exist_ok=True)
    results_path = run_dir / "results.jsonl"
    if not results_path.exists():
        results_path.touch()

    provers = selected_provers(args)
    lib.log(f"Run dir: {run_dir}")
    lib.log(f"Prefix: {prefix}")
    overall_rc = 0
    for prover in provers:
        for stage in stages:
            record = lib.run_stage(
                prover=prover,
                stage=stage,
                prefix=prefix,
                run_dir=run_dir,
                results_path=results_path,
                task=task_name,
                timeout_s=args.install_timeout_s if stage == "install" else args.check_timeout_s,
                cpu_seconds=getattr(args, stage + "_cpu_seconds", None),
                memory_bytes=getattr(args, stage + "_memory_bytes", None),
                max_log_bytes=getattr(args, "max_log_bytes", 1 << 20),
            )
            if record["status"] == "failed":
                overall_rc = 1
    summary = lib.write_summary(run_dir)
    lib.render_summary(summary)
    return overall_rc


def command_report(args: argparse.Namespace) -> int:
    if args.run_dir:
        run_dir = Path(args.run_dir).expanduser().resolve()
    else:
        candidates = sorted(
            (path for path in lib.RUNS_ROOT.iterdir() if path.is_dir()), reverse=True
        )
        if not candidates:
            lib.fail("no run directories found under itpeval/.runs")
        run_dir = candidates[0]
    summary = lib.write_summary(run_dir)
    if args.json:
        print(json.dumps(summary, indent=2, sort_keys=True))
    else:
        lib.render_summary(summary)
    return 0


def command_eval(args: argparse.Namespace) -> int:
    from itpeval.itp import run_itp  # noqa: PLC0415

    prefix = Path(args.prefix).expanduser().resolve()
    code_path = Path(args.file).expanduser().resolve() if args.file else None
    task_dir = Path(args.task_dir).expanduser().resolve() if args.task_dir else None
    task_file = Path(args.task_file).expanduser() if args.task_file else None

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
    except Exception as exc:
        lib.log(f"ERROR: {exc}")
        return 2

    payload = {
        "prover": result.prover,
        "ok": result.ok,
        "returncode": result.returncode,
        "duration_ms": result.duration_ms,
        "command": result.command,
        "workdir": str(result.workdir),
        "stdout": result.stdout,
        "stderr": result.stderr,
    }
    if args.json:
        print(json.dumps(payload, indent=2, sort_keys=True))
        return 0 if result.ok else 1

    stream = sys.stdout if result.ok else sys.stderr
    print(
        f"[ITPEval] prover={result.prover} ok={result.ok} rc={result.returncode} ms={result.duration_ms}",
        file=stream,
    )
    if result.stdout.strip():
        print("--- stdout ---", file=stream)
        print(result.stdout.rstrip(), file=stream)
    if result.stderr.strip():
        print("--- stderr ---", file=stream)
        print(result.stderr.rstrip(), file=stream)
    print(f"[ITPEval] workdir={result.workdir}", file=stream)
    return 0 if result.ok else 1


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(prog="itpeval", description="Shared ITPEval CLI")
    parser.add_argument(
        "--prefix",
        default=str(lib.default_prefix()),
        help="toolchain prefix (default: ITPEVAL_PREFIX, the selected user toolchains, or the checkout fallback)",
    )
    parser.add_argument("--run-dir", default=None, help="reuse a specific run directory")
    subparsers = parser.add_subparsers(dest="command", required=True)

    list_parser = subparsers.add_parser("list-provers", help="list available provers")
    list_parser.add_argument("provers", nargs="*", help="optional subset")
    list_parser.set_defaults(func=command_list_provers)

    for name, stages in (
        ("install", ("install",)),
        ("check", ("check",)),
        ("run", ("install", "check")),
    ):
        subparser = subparsers.add_parser(name, help=f"{name} selected provers")
        subparser.add_argument("provers", nargs="*", help="optional subset")
        subparser.add_argument("--install-timeout-s", type=float, help="deadline for each native installation")
        subparser.add_argument("--check-timeout-s", type=float, help="deadline for each native check")
        for stage in stages:
            subparser.add_argument(f"--{stage}-cpu-seconds", type=int, help="CPU seconds per native process")
            subparser.add_argument(f"--{stage}-memory-bytes", type=int, help="virtual address space per native process")
        subparser.add_argument("--max-log-bytes", type=int, default=1 << 20, help="retained bytes per stage log")
        if name in {"check", "run"}:
            subparser.add_argument(
                "--task",
                default="arith_2_plus_2",
                help="benchmark task name (default: arith_2_plus_2). Use 'hello' to run adapter hello/ checks.",
            )
        subparser.set_defaults(
            func=lambda args, _name=name, _stages=stages: command_stage(
                args, command_name=_name, stages=_stages
            )
        )

    report_parser = subparsers.add_parser("report", help="summarize a previous run")
    report_parser.add_argument("run_dir_arg", nargs="?", help="run directory to summarize")
    report_parser.add_argument("--json", action="store_true", help="print summary JSON")
    report_parser.set_defaults(func=command_report)

    eval_parser = subparsers.add_parser(
        "eval",
        help="evaluate a one-off file/snippet against a prover (wraps itpeval/itp.py)",
    )
    eval_parser.add_argument("--prover", required=True, help="prover name (e.g. rocq, lean4, isabelle)")
    eval_parser.add_argument(
        "--mode",
        default="raw",
        choices=("raw", "snippet"),
        help="how to interpret --code/--file (default: raw)",
    )
    eval_parser.add_argument("--timeout-s", type=int, default=None, help="timeout in seconds")
    eval_parser.add_argument(
        "--ensure-installed",
        action="store_true",
        help="run the prover's install.sh before checking",
    )
    eval_parser.add_argument("--json", action="store_true", help="print JSON result")
    source = eval_parser.add_mutually_exclusive_group(required=True)
    source.add_argument("--code", default=None, help="inline code (file contents or snippet)")
    source.add_argument("--file", default=None, help="path to a code file to run")
    source.add_argument(
        "--task-dir",
        default=None,
        help="pre-built task directory to run (must match the prover's check.sh expectations)",
    )
    eval_parser.add_argument("--task-file", default=None,
                             help="file inside --task-dir selected for the prover adapter")
    eval_parser.set_defaults(func=command_eval)

    add_commands(subparsers)
    add_toolchain_commands(subparsers)
    add_atp_commands(subparsers)
    return parser


def main(argv: list[str] | None = None) -> int:
    parser = build_parser()
    args = parser.parse_args(argv)
    if args.command == "report" and args.run_dir_arg and not args.run_dir:
        args.run_dir = args.run_dir_arg
    try:
        return int(args.func(args))
    except (OSError, ValueError, NotImplementedError) as exc:
        if args.command in {"prepare", "prepare-project", "extract", "verify-task", "dataset", "practice",
                            "training-data", "toolchains", "atp"}:
            parser.exit(2, f"itpeval {args.command}: {exc}\n")
        raise


__all__ = ["main", "build_parser"]
