from __future__ import annotations

import json
import os
import shutil
import subprocess
import sys
import time
from collections import Counter, defaultdict
from datetime import datetime, timezone
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
PROVERS_ROOT = ROOT / "provers"
RUNS_ROOT = ROOT / ".runs"
TASKS_ROOT = ROOT / "tasks"

DEFAULT_PROVERS = [
    "lean4",
    "rocq",
    "isabelle",
    "hol-light",
    "acl2", "agda", "hol4", "metamath", "mizar", "pvs",
]


def log(message: str) -> None:
    print(f"[ITPEval] {message}", file=sys.stderr)


def fail(message: str) -> "None":
    raise SystemExit(f"[ITPEval] ERROR: {message}")


def utc_timestamp() -> str:
    return datetime.now(timezone.utc).strftime("%Y%m%dT%H%M%SZ")


def utc_iso() -> str:
    return datetime.now(timezone.utc).isoformat(timespec="seconds")


def default_prefix() -> Path:
    env_prefix = os.environ.get("ITPEVAL_PREFIX")
    if env_prefix:
        return Path(env_prefix)
    # When the repo lives on EFS, large toolchains (opam/cabal) can become unusably slow
    # Prefer /tmp by default unless the user explicitly overrides via ITPEVAL_PREFIX/--prefix
    if str(ROOT).startswith("/efs/"):
        return Path("/tmp/itpeval-toolchains")
    return ROOT / "_toolchains"


def discover_provers() -> list[str]:
    ordered: list[str] = []
    seen: set[str] = set()
    for name in DEFAULT_PROVERS:
        if adapter_root(name).is_dir():
            ordered.append(name)
            seen.add(name)
    extras = sorted({
        path.name
        for path in PROVERS_ROOT.iterdir()
        if path.is_dir() and path.name not in seen
    })
    return ordered + extras


def adapter_root(prover: str) -> Path:
    return PROVERS_ROOT / prover


def stage_script(prover: str, stage: str) -> Path:
    return adapter_root(prover) / f"{stage}.sh"


def task_source_root(task: str) -> Path:
    return TASKS_ROOT / task


def create_run_dir(command: str, prefix: Path, task: str | None) -> Path:
    RUNS_ROOT.mkdir(parents=True, exist_ok=True)
    base_name = utc_timestamp()
    run_dir = RUNS_ROOT / base_name
    suffix = 1
    while run_dir.exists():
        run_dir = RUNS_ROOT / f"{base_name}-{suffix}"
        suffix += 1
    (run_dir / "logs").mkdir(parents=True, exist_ok=True)
    meta = {
        "command": command,
        "created_at": utc_iso(),
        "run_dir": str(run_dir),
        "prefix": str(prefix),
        "task": task,
    }
    (run_dir / "meta.json").write_text(
        json.dumps(meta, indent=2, sort_keys=True) + "\n", encoding="utf-8"
    )
    return run_dir


def append_jsonl(path: Path, record: dict) -> None:
    with path.open("a", encoding="utf-8") as handle:
        handle.write(json.dumps(record, sort_keys=True) + "\n")


def load_jsonl(path: Path) -> list[dict]:
    records: list[dict] = []
    if not path.exists():
        return records
    with path.open("r", encoding="utf-8") as handle:
        for raw_line in handle:
            line = raw_line.strip()
            if line:
                records.append(json.loads(line))
    return records


def prepare_task_stage(task: str, prover: str, run_dir: Path) -> Path | None:
    source_root = task_source_root(task)
    if not source_root.is_dir():
        fail(f"missing task directory: {source_root}")

    source_prover_root = source_root / prover
    if not source_prover_root.is_dir():
        return None

    stage_root = run_dir / "tasks" / task / "itpeval"
    stage_root.mkdir(parents=True, exist_ok=True)

    for filename in ("README.md", "task.json"):
        source_file = source_root / filename
        if source_file.is_file():
            destination_file = run_dir / "tasks" / task / filename
            destination_file.parent.mkdir(parents=True, exist_ok=True)
            shutil.copy2(source_file, destination_file)

    common_source = ROOT / "bin" / "common.sh"
    common_destination = stage_root / "bin" / "common.sh"
    common_destination.parent.mkdir(parents=True, exist_ok=True)
    shutil.copy2(common_source, common_destination)

    adapter_dir = adapter_root(prover)
    adapter_check_source = adapter_dir / "check.sh"
    staged_check = stage_root / "provers" / prover / "check.sh"
    staged_check.parent.mkdir(parents=True, exist_ok=True)
    shutil.copy2(adapter_check_source, staged_check)

    staged_hello = stage_root / "provers" / prover / "hello"
    if staged_hello.exists():
        shutil.rmtree(staged_hello)
    shutil.copytree(source_prover_root, staged_hello)
    return staged_check


def stage_result(
    *,
    prover: str,
    stage: str,
    task: str | None,
    status: str,
    returncode: int | None,
    log_path: Path,
    version: str | None = None,
    version_log_path: Path | None = None,
    started_at: str | None = None,
    ended_at: str | None = None,
    duration_ms: int | None = None,
    command: list[str] | None = None,
    skipped_reason: str | None = None,
) -> dict:
    record: dict = {
        "prover": prover,
        "stage": stage,
        "task": task,
        "status": status,
        "returncode": returncode,
        "log_path": str(log_path),
        "skipped_reason": skipped_reason,
    }
    if version is not None:
        record["version"] = version
    if version_log_path is not None:
        record["version_log_path"] = str(version_log_path)
    if started_at is not None:
        record["started_at"] = started_at
    if ended_at is not None:
        record["ended_at"] = ended_at
    if duration_ms is not None:
        record["duration_ms"] = duration_ms
    if command is not None:
        record["command"] = command
    return record


def run_stage(
    *,
    prover: str,
    stage: str,
    prefix: Path,
    run_dir: Path,
    results_path: Path,
    task: str | None,
) -> dict:
    script = stage_script(prover, stage)
    task_script: Path | None = None
    if stage == "check" and task is not None:
        task_script = prepare_task_stage(task, prover, run_dir)
        if task_script is None:
            record = stage_result(
                prover=prover,
                stage=stage,
                task=task,
                status="skipped",
                returncode=None,
                log_path=run_dir / "logs" / f"{prover}.{stage}.log",
                skipped_reason="missing_task_artifact",
            )
            append_jsonl(results_path, record)
            log(f"Skipping {prover} {stage}: task {task} has no artifact for this prover")
            return record
        script = task_script

    log_path = run_dir / "logs" / f"{prover}.{stage}.log"
    if not script.exists():
        record = stage_result(
            prover=prover,
            stage=stage,
            task=task,
            status="skipped",
            returncode=None,
            log_path=log_path,
            skipped_reason="missing_script",
        )
        append_jsonl(results_path, record)
        log(f"Skipping {prover} {stage}: missing {script}")
        return record

    env = os.environ.copy()
    env.update(
        {
            "ITPEVAL_PREFIX": str(prefix),
            "ITPEVAL_RUN_DIR": str(run_dir),
            "ITPEVAL_TASK": task or "",
            "ITPEVAL_STAGE": stage,
            "ITPEVAL_PROVER": prover,
            "ITPEVAL_LOG_FILE": str(log_path),
            "ITPEVAL_RESULTS_FILE": str(results_path),
            "ITPEVAL_TASK_ROOT": str(task_source_root(task)) if task else "",
        }
    )

    command = ["/bin/bash", str(script)]

    version_text: str | None = None
    version_log_path: Path | None = None
    if stage == "check":
        version_script = adapter_root(prover) / "version.sh"
        if version_script.exists():
            version_log_path = run_dir / "logs" / f"{prover}.version.log"
            try:
                completed_version = subprocess.run(
                    ["/bin/bash", str(version_script)],
                    env=env,
                    stdout=subprocess.PIPE,
                    stderr=subprocess.STDOUT,
                    check=False,
                )
                raw_version = completed_version.stdout.decode("utf-8", errors="replace").strip()
                version_log_path.write_text(raw_version + "\n", encoding="utf-8")
                if completed_version.returncode == 0:
                    version_text = raw_version
            except Exception:
                version_text = None

    started = time.time()
    started_at = utc_iso()
    log(f"=== {stage} {prover} ===")
    with log_path.open("wb") as log_handle:
        completed = subprocess.run(command, env=env, stdout=log_handle, stderr=subprocess.STDOUT)
    ended = time.time()
    ended_at = utc_iso()
    duration_ms = int((ended - started) * 1000)
    status = "ok" if completed.returncode == 0 else "failed"

    record = stage_result(
        prover=prover,
        stage=stage,
        task=task,
        status=status,
        returncode=completed.returncode,
        log_path=log_path,
        version=version_text,
        version_log_path=version_log_path,
        started_at=started_at,
        ended_at=ended_at,
        duration_ms=duration_ms,
        command=command,
    )
    append_jsonl(results_path, record)
    log(f"{stage} {prover}: {status} ({duration_ms} ms) log={log_path}")
    return record


def write_summary(run_dir: Path) -> dict:
    results_path = run_dir / "results.jsonl"
    summary_path = run_dir / "summary.json"
    records = load_jsonl(results_path)
    counts = Counter(record["status"] for record in records)
    by_stage: dict[str, Counter] = defaultdict(Counter)
    by_prover: dict[str, Counter] = defaultdict(Counter)
    task_name = None
    meta_path = run_dir / "meta.json"
    if meta_path.exists():
        try:
            task_name = json.loads(meta_path.read_text(encoding="utf-8")).get("task")
        except Exception:
            task_name = None
    for record in records:
        by_stage[record["stage"]][record["status"]] += 1
        by_prover[record["prover"]][record["status"]] += 1
    summary = {
        "run_dir": str(run_dir),
        "results_file": str(results_path),
        "generated_at": utc_iso(),
        "task": task_name,
        "total": len(records),
        "counts": dict(counts),
        "by_stage": {stage: dict(counter) for stage, counter in by_stage.items()},
        "by_prover": {prover: dict(counter) for prover, counter in by_prover.items()},
        "records": records,
    }
    summary_path.write_text(json.dumps(summary, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    return summary


def render_summary(summary: dict) -> None:
    print(f"run_dir: {summary['run_dir']}")
    if summary.get("task"):
        print(f"task: {summary['task']}")
    counts = summary.get("counts", {})
    print("counts: " + ", ".join(f"{name}={counts.get(name, 0)}" for name in ("ok", "failed", "skipped")))
    print("records:")
    for record in summary.get("records", []):
        duration = record.get("duration_ms")
        duration_text = f"{duration}ms" if duration is not None else "-"
        print(f"  {record['stage']:>6} {record['prover']:<12} {record['status']:<7} {duration_text:>8} {record['log_path']}")
