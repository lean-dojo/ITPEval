"""CLI bindings for the public environment, extraction and verification services."""
from __future__ import annotations

import json
import os
from pathlib import Path

from itpeval.backends.projects import build_task
from itpeval.backends.registry import curated_project, project_prover_ids, prover_ids
from itpeval.cli.practice import create_practice
from itpeval.core.types import Artifact
from itpeval.environments import load_project, prepare_manifest, prepare_project
from itpeval.environments.cache import write_json
from itpeval.runtime.sessions import DocumentCheckpoint, DocumentSession
from itpeval.verification import candidate_from_bytes


def _prepare(args):
    if args.manifest:
        if args.prover or args.project or args.library or args.option or args.import_name or args.toolchain_input:
            raise ValueError("--manifest selects the prover, project, libraries, imports and options")
        locked = prepare_manifest(args.manifest, prefix=Path(args.prefix), cache=args.cache)
    else:
        if not args.prover:
            raise ValueError("choose a prover or pass --manifest")
        if args.prover not in prover_ids() and args.project is None:
            raise ValueError("a typed adapter needs --project or an environment manifest")
        project = args.project or curated_project(args.prover)
        locked = prepare_project(args.prover, project, prefix=Path(args.prefix), cache=args.cache,
                                 libraries=_pairs(args.library, Path), options=_pairs(args.option, str),
                                 imports=args.import_name, toolchain_inputs=_pairs(args.toolchain_input, Path))
    print(json.dumps({"environment_id": locked.environment_id, "lock_path": str(locked.lock_path)}))
    return 0


def _pairs(pairs, convert):
    result = {}
    for item in pairs:
        key, sep, value = item.partition("=")
        if not (sep and key and value) or key in result:
            raise ValueError(f"expected a unique NAME=VALUE pair: {item!r}")
        result[key] = convert(value)
    return result


def _verify(args):
    prepared = load_project(args.lock)
    task = build_task(prepared, args.manifest)
    options = {"retain_dir": args.retain_dir}
    if args.checkpoint is not None:
        checkpoint = DocumentCheckpoint.from_dict(json.loads(args.checkpoint.read_bytes()))
        session, evidence = DocumentSession.from_checkpoint(task, prepared, checkpoint, **options)
        if evidence is None:
            evidence = session.finalize(session.handle, **options)
    else:
        session = DocumentSession(task, prepared)
        if args.artifact_json is not None:
            artifact = Artifact.from_dict(json.loads(args.artifact_json.read_bytes()))
            _, evidence = session.submit_document(session.handle, artifact, **options)
        elif args.document_file is not None:
            _, evidence = session.submit_document(session.handle, args.document_file.read_bytes(), **options)
        else:
            candidate = args.candidate
            if args.candidate_file is not None:
                candidate = (candidate_from_bytes(task, args.candidate_file.read_bytes()) if task.is_detached_certificate
                             else args.candidate_file.read_text(encoding="utf-8"))
            _, evidence = session.submit(session.handle, candidate, **options)
    if args.save_checkpoint is not None:
        write_json(args.save_checkpoint, session.checkpoint(session.handle).to_dict())
    if args.summary:
        verdict = evidence.checker_outcome
        if evidence.task_success is None:
            verdict = f"{evidence.execution_outcome} ({verdict})"
        print(f"{task.prover} · {task.targets[0]} · {verdict}")
        if evidence.task_success is not True:
            for log in (evidence.stdout, evidence.stderr):
                if log.strip():
                    print(log.strip()[-1800:])
    else:
        print(json.dumps(evidence.to_dict(), sort_keys=True, ensure_ascii=False))
    return {True: 0, False: 1, None: 2}[evidence.task_success]


def _extract(args):
    from itpeval.extraction import extract_project
    result = extract_project(load_project(args.lock), args.entrypoint, args.output,
                             timeout_s=args.timeout_s, context_storage=args.context_storage)
    print(json.dumps({"path": str(result.path), "cache_hit": result.cache_hit,
                      "report": result.report}, sort_keys=True, ensure_ascii=False))
    return 0


def _dataset(args):
    from itpeval.corpus.datasets import export_dataset
    from itpeval.corpus.example import ENTRY, LIBRARY
    from itpeval.corpus.parquet import export_parquet

    if args.format == "parquet":
        try:
            import pyarrow.parquet  # noqa: F401
        except ImportError as exc:
            raise ValueError("Parquet export requires the itpeval[parquet] extra") from exc
    if args.lock:
        if args.project or args.prover or not args.entrypoint:
            raise ValueError("use --lock with --entrypoint for a prepared project")
        prepared = load_project(args.lock)
        entrypoint = args.entrypoint
    else:
        if not args.prover or (args.project and not args.entrypoint):
            raise ValueError("choose a prover and supply --entrypoint for a custom project")
        if args.prover not in prover_ids() and args.project is None:
            raise ValueError("a typed adapter needs --project and --entrypoint")
        project = args.project or LIBRARY / args.prover / "library"
        prepared = prepare_project(args.prover, project, prefix=Path(args.prefix), cache=args.cache)
        entrypoint = args.entrypoint or ENTRY[args.prover]
    result, premises = export_dataset(prepared, entrypoint, args.output, timeout_s=args.timeout_s,
                                     context_storage=args.context_storage, premise_visibility=args.premise_visibility)
    paths = {"declarations": result.path / "declarations.jsonl", "premises": premises}
    if args.format == "parquet":
        for view, source in paths.copy().items():
            filename = source.stem if view == "premises" else f"{result.path.name}.{view}"
            destination = args.output / f"{filename}.parquet"
            export_parquet(source, destination, view=view)
            paths[view] = destination
    print(json.dumps({"bundle": str(result.path), "count": result.report["declarations"],
                      **{view: str(path.resolve()) for view, path in paths.items()}}))
    return 0


def add_commands(commands):
    cache_home = Path(os.environ.get("XDG_CACHE_HOME", Path.home() / ".cache"))
    practice = commands.add_parser("practice", help="create a VS Code workspace for a packaged completion exercise")
    practice.add_argument("prover", choices=prover_ids())
    practice.add_argument("--output", type=Path, help="new workspace directory (default: build/practice/PROVER)")
    practice.add_argument("--cache", type=Path, default=cache_home / "itpeval/prepared")
    practice.set_defaults(func=create_practice)

    dataset = commands.add_parser("dataset", help="export declarations and premise-selection records")
    dataset.add_argument("prover", choices=project_prover_ids(), nargs="?")
    dataset.add_argument("--project", type=Path, help="defaults to the prover's bundled library example")
    dataset.add_argument("--lock", type=Path, help="reuse a prepared environment with library dependencies")
    dataset.add_argument("--entrypoint", help="source file relative to the project root")
    dataset.add_argument("--cache", type=Path, default=cache_home / "itpeval/prepared")
    dataset.add_argument("--output", type=Path, required=True)
    dataset.add_argument("--timeout-s", type=float, default=180, help="native extraction timeout in seconds")
    dataset.add_argument("--format", choices=("jsonl", "parquet"), default="jsonl")
    dataset.add_argument("--context-storage", choices=("expanded", "compact"), default="expanded",
                         help="store Metamath visibility as shared assertion prefixes with compact")
    dataset.add_argument("--premise-visibility", choices=("expanded", "reference"),
                         help="write visibility inline or reference each context (compact defaults to reference)")
    dataset.set_defaults(func=_dataset)

    from itpeval.corpus import benchmark_training, library_collection
    from itpeval.learning import training_data

    training = commands.add_parser("training-data", help="write dataset views for model training and evaluation")
    sources = training.add_subparsers(dest="source", required=True)
    native = sources.add_parser("native", help="export training views from extraction bundles or proof episodes")
    training_data.add_arguments(native)
    native.set_defaults(func=training_data.run_command)
    libraries = sources.add_parser("libraries", help="combine declarations and premise records across libraries")
    library_collection.add_arguments(libraries)
    libraries.set_defaults(func=library_collection.run_command)
    benchmark = sources.add_parser("benchmark", help="export evaluation references from the released benchmark")
    benchmark_training.add_arguments(benchmark)
    benchmark.set_defaults(func=benchmark_training.run_command)

    prepare = commands.add_parser("prepare", aliases=["prepare-project"], help="lock a project and its installed native toolchain")
    prepare.add_argument("prover", choices=project_prover_ids(), nargs="?")
    prepare.add_argument("--manifest", type=Path, help="resolve an environment manifest")
    prepare.add_argument("--project", type=Path, help="defaults to the packaged completion fixture")
    prepare.add_argument("--cache", type=Path, required=True)
    prepare.add_argument("--library", action="append", default=[], metavar="NAME=PATH")
    prepare.add_argument("--toolchain-input", action="append", default=[], metavar="ROLE=PATH",
                         help="bind an additional native instrument or runtime to the lock")
    prepare.add_argument("--option", action="append", default=[], metavar="NAME=VALUE")
    prepare.add_argument("--import-name", action="append", default=[])
    prepare.set_defaults(func=_prepare)

    verify_cmd = commands.add_parser("verify-task", help="check a proof fragment or full document against a locked task")
    verify_cmd.add_argument("--lock", type=Path, required=True)
    verify_cmd.add_argument("--manifest", default="completion.json")
    verify_cmd.add_argument("--retain-dir", type=Path)
    verify_cmd.add_argument("--summary", action="store_true", help="show the verdict and failure diagnostics as text")
    verify_cmd.add_argument("--save-checkpoint", type=Path, help="write the submitted revision and task identity as JSON")
    source = verify_cmd.add_mutually_exclusive_group(required=True)
    source.add_argument("--candidate")
    source.add_argument("--candidate-file", type=Path)
    source.add_argument("--document-file", type=Path, help="full revised entrypoint; retain all locked siblings")
    source.add_argument("--artifact-json", type=Path, help="complete Artifact.to_dict() JSON file")
    source.add_argument("--checkpoint", type=Path, help="saved document checkpoint for this locked task")
    verify_cmd.set_defaults(func=_verify)

    extract = commands.add_parser("extract", help="extract native declarations from a locked project")
    extract.add_argument("--lock", type=Path, required=True)
    extract.add_argument("--entrypoint", required=True)
    extract.add_argument("--output", type=Path, required=True)
    extract.add_argument("--timeout-s", type=float, default=180)
    extract.add_argument("--context-storage", choices=("expanded", "compact"), default="expanded",
                         help="store Metamath visibility as shared assertion prefixes with compact")
    extract.set_defaults(func=_extract)
