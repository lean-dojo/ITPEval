"""CLI commands for standalone ATP runs and native proof replay."""

from __future__ import annotations

import argparse
import json
import sys
from contextlib import ExitStack
from pathlib import Path

from itpeval.backends.projects import build_task, project_file
from itpeval.core.types import Budgets
from itpeval.environments import load_project, prepare_project
from itpeval.environments.cache import write_json

from .isabelle import run_sledgehammer
from .lean import LeanHornProblem, run_horn_search
from .rocq import RocqHornProblem, run_rocq_horn_search
from .search import SOLVERS, prepare_solver, solve_tptp


def _print_evidence(args, evidence, *, task=None):
    data = evidence.to_dict()
    if args.output is not None:
        write_json(args.output, data)
    print(json.dumps(data, ensure_ascii=False))
    if task is not None and args.episodes_output is not None:
        from itpeval.learning.assisted import episode_from_search
        from itpeval.learning.episodes import export_jsonl

        episode = episode_from_search(task, evidence)
        export_jsonl([episode] if episode is not None else [], args.episodes_output, view="episodes")


def _solve(args):
    evidence = solve_tptp(
        args.problem, solver=args.solver, executable=args.executable, prefix=args.prefix,
        tptp_root=args.tptp_root, budgets=Budgets(timeout_s=args.timeout_s, max_log_bytes=args.max_log_bytes,
                                                 cpu_seconds=args.cpu_seconds, memory_bytes=args.memory_bytes),
    )
    _print_evidence(args, evidence)
    if evidence.conclusive:
        return 0
    return 2 if evidence.outcome in {"solver_error", "protocol_error", "crash", "unavailable_environment"} else 1


def _require_distinct_outputs(args):
    if (args.output is not None and args.episodes_output is not None
            and args.output.resolve() == args.episodes_output.resolve()):
        raise ValueError("search evidence and proof episodes must have distinct output paths")


def _hammer(args):
    _require_distinct_outputs(args)
    if args.demo:
        root = Path(__file__).resolve().parents[1] / "tests/fixtures/projects/isabelle/hammer"
        prepared = prepare_project("isabelle", root, prefix=args.prefix, cache=args.cache)
    else:
        prepared = load_project(args.lock)
    task = build_task(prepared, args.manifest)
    evidence = run_sledgehammer(task, prepared=prepared, solver=args.solver, search_timeout_s=args.timeout_s,
                               solver_timeout_s=args.solver_timeout_s, replay_limit=args.replay_limit,
                               trace_premises=args.trace_premises)
    _print_evidence(args, evidence, task=task)
    if evidence.checked_proof:
        return 0
    if evidence.search_diagnostic:
        print(evidence.search_diagnostic, file=sys.stderr)
    return 2 if evidence.search_outcome in {
        "search_error", "crash", "unavailable_environment", "unsupported_toolchain",
    } else 1


def _horn(args):
    _require_distinct_outputs(args)
    if args.demo:
        root = Path(__file__).resolve().parents[1] / "tests/fixtures/projects" / args.horn_prover / "horn"
        prepared = prepare_project(args.horn_prover, root, prefix=args.prefix, cache=args.cache)
    else:
        prepared = load_project(args.lock)
    task = build_task(prepared, args.manifest)
    problem = None
    if not args.auto:
        problem_path = args.problem if args.problem is not None else project_file(prepared.project, "horn.json")
        try:
            problem = args.horn_problem.from_dict(json.loads(problem_path.read_bytes()))
        except (TypeError, ValueError) as error:
            raise ValueError(f"invalid Horn problem in {problem_path}: {error}") from error
    solver = prepare_solver(args.solver, executable=args.executable, prefix=prepared.prefix)
    evidence = args.horn_search(task, problem, prepared=prepared, solver=solver,
                                search_timeout_s=args.timeout_s)
    _print_evidence(args, evidence, task=task)
    if evidence.replay_outcome == "accepted":
        return 0
    failures = {"solver_error", "protocol_error", "crash", "unavailable_environment"}
    return 2 if evidence.search.outcome in failures or evidence.replay_outcome in failures else 1


def _resume(args):
    from itpeval.atp.session import ATP_SESSION_PROVERS
    from itpeval.runtime.proof_driver import NativeProofCheckpoint, NativeProofDriver

    if args.output is not None and args.output.resolve() in {args.checkpoint.resolve(), args.lock.resolve()}:
        raise ValueError("write the search receipt to a path distinct from the checkpoint and project lock")
    prepared = load_project(args.lock)
    task = build_task(prepared, args.manifest)
    if task.prover not in ATP_SESSION_PROVERS:
        raise ValueError(f"ATP checkpoint search is unavailable for {task.prover}")
    checkpoint = NativeProofCheckpoint.from_dict(json.loads(args.checkpoint.read_bytes()))
    with ExitStack() as stack:
        options = {}
        if task.prover == "hol-light":
            from itpeval.backends.hol_light.worker import ForkedHOLLight

            if ForkedHOLLight.supports_project(prepared):
                options["worker"] = stack.enter_context(ForkedHOLLight(prepared))
        driver = NativeProofDriver.from_checkpoint(task, prepared, checkpoint, **options)
        suggestion = driver.suggest_atp(solver=args.solver, executable=args.executable,
                                        timeout_s=args.timeout_s, goal_path=args.goal_path, max_trials=args.max_trials,
                                        hints=tuple(args.hint), proof_fragment=args.proof_file.read_text().rstrip("\n")
                                        if args.proof_file is not None else None)
    _print_evidence(args, suggestion)
    if suggestion.outcome in {"accepted", "progress"}:
        return 0
    return 2 if suggestion.outcome in {"solver_error", "protocol_error", "search_error", "crash",
                                       "unavailable_environment", "unsupported_toolchain"} else 1


def _parse_goal_path(text):
    if text == "root":
        return ()
    parts = text.split(".")
    if not all(part.isascii() and part.isdigit() and len(part) <= 3 for part in parts):
        raise argparse.ArgumentTypeError("use root or a dotted sequence of goal indices, for example 0.1")
    return tuple(map(int, parts))


def add_commands(commands):
    _add_actions(commands.add_parser("atp", help="run automated proof search"))


def _add_actions(parser):
    actions = parser.add_subparsers(dest="atp_action", required=True)
    solve = actions.add_parser("solve", help="ask a local automated prover about a TPTP problem")
    solve.add_argument("solver", choices=SOLVERS)
    solve.add_argument("problem", type=Path, help="input TPTP problem")
    solve.add_argument("--executable", type=Path, help="override automated prover discovery")
    solve.add_argument("--tptp-root", type=Path, help="root for includes and the input problem")
    solve.add_argument("--timeout-s", type=float, default=30, help="supervised wall deadline")
    solve.add_argument("--cpu-seconds", type=int, help="CPU budget per process")
    solve.add_argument("--memory-bytes", type=int, help="address-space budget per process")
    solve.add_argument("--max-log-bytes", type=int, default=1 << 20, help="retained bytes per output stream")
    solve.add_argument("--output", type=Path, help="also store the evidence as JSON")
    solve.set_defaults(func=_solve)

    hammer = actions.add_parser("hammer", help="search a locked Isabelle goal and replay permitted suggestions")
    source = hammer.add_mutually_exclusive_group(required=True)
    source.add_argument("--lock", type=Path, help="prepared Isabelle project lock")
    source.add_argument("--demo", action="store_true", help="run the bundled list theorem")
    hammer.add_argument("--cache", type=Path, default=Path.home() / ".cache/itpeval/prepared", help="cache for --demo")
    hammer.add_argument("--manifest", default="completion.json", help="relative proof task manifest")
    hammer.add_argument("--solver", choices=SOLVERS, default="e")
    hammer.add_argument("--timeout-s", type=float, default=30, help="supervised search wall deadline")
    hammer.add_argument("--solver-timeout-s", type=int, default=5, help="native Sledgehammer solver timeout")
    hammer.add_argument("--replay-limit", type=int, default=4, help="maximum allowed suggestions to check")
    hammer.add_argument("--trace-premises", action=argparse.BooleanOptionalAction, default=True,
                        help="record Sledgehammer's candidate premise pools")
    hammer.add_argument("--output", type=Path, help="also store the evidence as JSON")
    hammer.add_argument("--episodes-output", type=Path, help="store replayed suggestions as proof episodes in JSONL")
    hammer.set_defaults(func=_hammer)

    _add_horn_action(actions, "lean-horn", "lean4", "Lean", LeanHornProblem, run_horn_search)
    _add_horn_action(actions, "rocq-horn", "rocq", "Rocq", RocqHornProblem, run_rocq_horn_search)
    resume = actions.add_parser("resume", help="search an open goal from a saved native proof checkpoint")
    resume.add_argument("--lock", type=Path, required=True, help="prepared project lock")
    resume.add_argument("--checkpoint", type=Path, required=True, help="JSON native proof checkpoint")
    resume.add_argument("--manifest", default="completion.json", help="relative proof task manifest")
    resume.add_argument("--solver", choices=(*SOLVERS, "native"), help="default to E or the native HOL tactic")
    resume.add_argument("--goal-path", type=_parse_goal_path, help="choose a pending HOL branch, for example 0.1")
    resume.add_argument("--executable", type=Path, help="override solver discovery for Lean and Rocq")
    resume.add_argument("--timeout-s", type=float, help="wall deadline for each discovery or search phase")
    resume.add_argument("--max-trials", type=int, default=32, help="limit candidate trials for a bounded native search")
    resume.add_argument("--hint", action="append", default=[], help="supply a named Agda Auto hint")
    resume.add_argument("--proof-file", type=Path, help="reviewed ProofLite fragment for complete PVS checking")
    resume.add_argument("--output", type=Path, help="also store the revision-bound search receipt as JSON")
    resume.set_defaults(func=_resume)


def _add_horn_action(actions, command, prover, language, problem_type, search):
    help_text = f"search and replay an explicit ground Horn problem in locked {language}"
    horn = actions.add_parser(command, help=help_text)
    source = horn.add_mutually_exclusive_group(required=True)
    source.add_argument("--lock", type=Path, help=f"prepared {language} project lock")
    source.add_argument("--demo", action="store_true", help="run the bundled delivery theorem")
    horn.add_argument("--cache", type=Path, default=Path.home() / ".cache/itpeval/prepared", help="cache for --demo")
    horn.add_argument("--manifest", default="completion.json", help="relative proof task manifest")
    problem = horn.add_mutually_exclusive_group()
    problem.add_argument("--problem", type=Path, help="Horn JSON file (default is horn.json in the locked project)")
    problem.add_argument("--auto", action="store_true", help=f"discover supported clauses from the native {language} goal")
    horn.add_argument("--solver", choices=SOLVERS, default="e")
    horn.add_argument("--executable", type=Path, help="override automated prover discovery")
    horn.add_argument("--timeout-s", type=float, help="wall deadline for each discovery or search phase")
    horn.add_argument("--output", type=Path, help="also store the evidence as JSON")
    horn.add_argument("--episodes-output", type=Path, help="store native replay as a proof episode in JSONL")
    horn.set_defaults(func=_horn, horn_prover=prover, horn_problem=problem_type, horn_search=search, auto=False)


def main(argv=None):
    from itpeval.cli.lib import default_prefix

    parser = argparse.ArgumentParser(prog="python -m itpeval.atp")
    parser.add_argument("--prefix", default=default_prefix(), type=Path)
    _add_actions(parser)
    args = parser.parse_args(argv)
    try:
        return args.func(args)
    except (OSError, ValueError) as error:
        parser.exit(2, f"{parser.prog}: {error}\n")
