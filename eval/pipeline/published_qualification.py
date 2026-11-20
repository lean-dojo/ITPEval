"""Reproduce a prerecorded published MiniF2F translation through all three evaluation entry points."""

import argparse
import json
import tempfile
from pathlib import Path

from eval.pipeline.config import STMTS_JSON
from eval.pipeline.records import translation_custom_id
from eval.pipeline.translation.batch_jobs import save_job
from eval.pipeline.translation.batch_run import main as batch
from eval.pipeline.translation.data import load_pairs
from eval.pipeline.translation.run import main as sync
from eval.pipeline.translation.verify_generated import main as posthoc
from itpeval.core.records import digest


def qualify(output: Path):
    item = next(r for r in json.loads(STMTS_JSON.read_bytes()) if r["title"] == "mathd_numbertheory_342"
                and r["source"] == "minif2f" and r["prover"] == "rocq")
    pair = next(p for p in load_pairs(corpus="published", sources=[item["source"]], theorem_ids=[item["theorem_id"]])
                if (p["src_prover"], p["tgt_prover"]) == ("lean4", "rocq"))
    conditions = ["--corpus", "published", "--sources", item["source"], "--ids", str(item["theorem_id"]),
                  "--src", pair["src_prover"], "--tgt", pair["tgt_prover"]]
    # Adjust the archived import to the pinned Rocq Stdlib namespace.
    candidate = item["content"].replace("Require Import Arith.", "From Stdlib Require Import Arith.")
    raw = "```coq\n" + candidate + "\n```"
    with tempfile.TemporaryDirectory() as directory:
        work = Path(directory)
        responses = work / "responses.json"
        save_job(responses, {translation_custom_id(pair): raw})
        settings = [*conditions, "--responses", str(responses)]
        sync([*settings, "--output", str(work / "sync.jsonl")])
        sync([*settings, "--no-verify", "--output", str(work / "generated.jsonl")])
        posthoc([str(work / "generated.jsonl"), "--output-dir", str(work / "posthoc")])
        job = str(work / "batch.json")
        batch(["submit", *settings, "--job-file", job])
        batch(["collect", job, "--output", str(work / "batch.jsonl")])
        rows = {key: json.loads((work / file).read_bytes()) for key, file in
                (("sync", "sync.jsonl"), ("batch", "batch.jsonl"), ("posthoc", "posthoc/generated.jsonl"))}
        report = {"schema_version": 1, "population": "published", "transport": "prerecorded",
                  "source": pair, "archived_reference": item["content"], "raw_generated": raw, "routes": rows}
        for row in rows.values():
            evidence = row["evidence"]
            if (row["raw_generated"] != raw or row["generated"].strip() != candidate.strip()
                    or row["verified"] is not True or row["task_success"] is not None
                    or evidence["completion_status"] != "statement_accepted"
                    or evidence["target_preservation"] != "unbound"):
                raise RuntimeError(f"published translation route disagrees: {row}")
        report["candidate_id"] = digest(candidate)
        save_job(output, report, indent=2)


if __name__ == "__main__":
    cli = argparse.ArgumentParser(description=__doc__)
    cli.add_argument("--output", type=Path, required=True)
    qualify(cli.parse_args().output)
