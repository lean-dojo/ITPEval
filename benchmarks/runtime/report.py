"""Render published Linux performance tables from the native JSON measurements."""
import argparse
import json
import re
from statistics import median
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
RAW = ROOT / "benchmarks/runtime"
DOCS = ROOT / "docs/runtime/measurements"


def table(path):
    parts = [
        "| Prover | First check (s) | Repeat (s) | Invalid (s) | Peak RSS (MiB) | 1 worker (jobs/s) | 2 workers (jobs/s) | Crashes / timeouts |",
        "| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: |",
    ]
    for row in sorted((json.loads(line) for line in path.read_text().splitlines()), key=lambda r: r["prover"]):
        samples = {s["workload"]: s for s in row["samples"]}
        elapsed = [samples[k]["checker_ms"] / 1000 for k in ("first_check", "warm_check", "rejected_attempt")]
        rss = max(s["peak_process_rss_bytes"] for s in samples.values()) / 1024**2
        runs = {r["workers"]: r for r in row["runs"]}
        if not all(r["correct"] and r["agreement"] for r in runs.values()):
            raise ValueError("cannot report successful qualification for " + row["prover"])
        crashes = sum(r["crashes"] for r in runs.values())
        timeouts = sum(r["timeouts"] for r in runs.values())
        parts.append(f'| {row["prover"]} | {elapsed[0]:.3f} | {elapsed[1]:.3f} | {elapsed[2]:.3f} | '
                     f'{rss:.1f} | {runs[1]["attempts_per_second"]:.3f} | {runs[2]["attempts_per_second"]:.3f} | '
                     f'{crashes} / {timeouts} |')
    return "\n".join(parts)


def startup_table():
    lines = ["| Prover | First launch (s) | Repeat launch (s) |", "| --- | ---: | ---: |"]
    for path in sorted((RAW / "startup-linux-x86_64").glob("*.json")):
        row = json.loads(path.read_bytes())
        a, b = row["samples"]
        lines.append(f'| {row["prover"]} | {a["native_ms"] / 1000:.3f} | {b["native_ms"] / 1000:.3f} |')
    return "\n".join(lines)


def cache_table():
    report = json.loads((RAW / "cache-latency.json").read_bytes())
    expected = sorted(path.stem for path in (RAW / "startup-linux-x86_64").glob("*.json"))
    if sorted(row["prover"] for row in report["rows"]) != expected:
        raise ValueError("cache measurements and startup measurements cover different provers")
    lines = ["| Prover | First prepare (s) | Repeat prepare (s) | Load lock (s) | Miss (s) | Hit (s) | Miss / hit |",
             "| --- | ---: | ---: | ---: | ---: | ---: | ---: |"]
    for row in sorted(report["rows"], key=lambda row: row["prover"]):
        samples = row["samples"]
        if len(samples) != 3 or report["repeats"] != len(samples):
            raise ValueError("the published protocol requires three paired cache trials per prover")
        repeat, load, miss, hit = (median(s[key] for s in samples)
                                   for key in ("repeat_prepare_s", "load_lock_s", "miss_s", "hit_s"))
        lines.append(f'| {row["prover"]} | {row["first_prepare_s"]:.3f} | {repeat:.3f} | {load:.3f} | '
                     f'{miss:.3f} | {hit:.3f} | {miss / hit:.1f}× |')
    return "\n".join(lines)


def verifier_table():
    report = json.loads((RAW / "metamath-verifiers.json").read_bytes())
    lines = ["| Database | Proofs | Metamath (s) | ITPEval (s) | mmverify.py (s) |",
             "| --- | ---: | ---: | ---: | ---: |"]
    for row in report["rows"]:
        if len(row["wall_seconds"]) != 3:
            raise ValueError("the published verifier comparison requires three trials per database")
        times = [median(trial[method] for trial in row["wall_seconds"])
                 for method in ("metamath", "itpeval", "mmverify")]
        lines.append(f'| {row["source"]} | {row["proofs"]:,} | ' + " | ".join(f"{t:.3f}" for t in times) + " |")
    return "\n".join(lines)


def scale_table(*reports):
    lines = ["| Prover | Jobs per run | 1 worker (jobs/s) | 4-worker cap (jobs/s) | Batch speedup | p95 at 4 (s) | Peak process RSS at 4 (MiB) |",
             "| --- | ---: | ---: | ---: | ---: | ---: | ---: |"]
    entries = (row for report in reports for row in json.loads(report.read_bytes())["provers"])
    for row in sorted(entries, key=lambda entry: entry["prover"]):
        one, four = row["samples"]
        count = len(row["jobs"])
        if (one["workers"], four["workers"], one["correct"], four["correct"]) != (1, 4, count, count):
            raise ValueError("missing worker comparison or unexpected verdict for " + row["prover"])
        speedup = one["wall_s"] / four["wall_s"]
        rss = four["peak_native_process_rss_bytes"] / 1024**2
        lines.append(f'| {row["prover"]} | {count} | {one["attempts_per_second"]:.3f} | '
                     f'{four["attempts_per_second"]:.3f} | {speedup:.2f}× | '
                     f'{four["p95_time_to_verdict_s"]:.3f} | {rss:.1f} |')
    return "\n".join(lines)


def render():
    # Keep hand-edited methods and citations in the docs. Only the tables are generated.
    chapters = {
        "startup-and-caching.md": {"startup": startup_table(), "cache": cache_table()},
        "libraries.md": {"library": table(RAW / "library-linux-x86_64.jsonl"), "verifiers": verifier_table()},
        "throughput.md": {
            "completion": table(RAW / "linux-x86_64.jsonl"),
            "scale": scale_table(RAW / "scalability-hol-light.json", RAW / "scalability-nine.json"),
            "scale_extended": scale_table(RAW / "scalability-extended.json"),
        },
    }
    rendered = {}
    for chapter, tables in chapters.items():
        path = DOCS / chapter
        content = path.read_text(encoding="utf-8")
        for name, values in tables.items():
            start, end = f"<!-- table:{name} -->", f"<!-- end:{name} -->"
            content, count = re.subn(f"{start}.*?{end}", f"{start}\n{values}\n{end}", content, flags=re.S)
            if count != 1:
                raise ValueError(f"expected one {name} table in {path}")
        rendered[chapter] = content
    return rendered


if __name__ == "__main__":
    cli = argparse.ArgumentParser(description=__doc__)
    cli.add_argument("--output", type=Path, default=DOCS, help="directory for the rendered chapters")
    cli.add_argument("--check", action="store_true")
    args = cli.parse_args()
    chapters = render()
    if args.check:
        raise SystemExit(0 if all((args.output / name).read_text(encoding="utf-8") == text
                                  for name, text in chapters.items()) else 1)
    args.output.mkdir(parents=True, exist_ok=True)
    for name, text in chapters.items():
        (args.output / name).write_text(text, encoding="utf-8")
