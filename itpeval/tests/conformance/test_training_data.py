"""Test trainer views built from recorded checks and content-addressed sources."""

import importlib.util
import json
from pathlib import Path
from tempfile import TemporaryDirectory
import unittest
from unittest.mock import patch

from itpeval.core.types import TaskSpec
from itpeval.corpus.storage import jsonl, read_jsonl, store_blob
from itpeval.learning.training_data import export_training_data
from itpeval.verification.service import assemble


ROOT = Path(__file__).resolve().parents[3]
EVIDENCE = ROOT / "benchmarks/runtime/evidence/lean4"


def lean_episode():
    conformance = json.loads((EVIDENCE / "conformance.json").read_bytes())
    return json.loads((EVIDENCE / conformance["episode"]).read_bytes())


class TrainingDataTest(unittest.TestCase):
    @unittest.skipUnless((EVIDENCE / "conformance.json").is_file(), "requires repository evidence")
    def test_aligned_episode_views_with_chat_and_parquet(self):
        episode = lean_episode()
        with_parquet = importlib.util.find_spec("pyarrow")
        with TemporaryDirectory() as tmp:
            root = Path(tmp)
            source, duplicate = root / "episode.jsonl", root / "duplicate.jsonl"
            for path in (source, duplicate):
                jsonl(path, [episode])
            out = root / "export"
            result = export_training_data(
                out, episodes=[source, duplicate], format="both" if with_parquet else "jsonl", style="chat",
            )
            self.assertEqual(result["views"], {
                "pretraining": 0, "retrieval": 0, "sft": 1, "repair": 1, "preference": 1,
                "unpaired": 2, "grpo": 1, "trajectory": 2,
            })
            if with_parquet:
                import pyarrow.parquet as pq

                for view, count in result["views"].items():
                    if count:
                        rows = list(read_jsonl(out / f"{view}.jsonl"))
                        self.assertEqual(rows, pq.read_table(out / f"{view}.parquet").to_pylist())
            pair, = read_jsonl(out / "preference.jsonl")
            self.assertEqual(pair["chosen"], [{"role": "assistant", "content": "rfl"}])
            self.assertEqual(pair["rejected"], [{"role": "assistant", "content": "exact False.elim"}])
            prompt = pair["prompt"][0]["content"]
            self.assertIn("<PROOF>", prompt)
            self.assertNotIn("rfl", prompt)
            self.assertNotIn("exact False.elim", prompt)
            repair, = read_jsonl(out / "repair.jsonl")
            self.assertIn("exact False.elim", repair["prompt"][0]["content"])
            self.assertIn("Checker verdict: rejected", repair["prompt"][0]["content"])
            first, last = read_jsonl(out / "trajectory.jsonl")
            self.assertEqual((first["terminated"], first["truncated"]), (False, False))
            self.assertEqual((last["terminated"], last["truncated"]), (True, False))

    @unittest.skipUnless((EVIDENCE / "conformance.json").is_file(), "requires repository evidence")
    def test_unknown_episode_only_supplies_prompt_and_unscored_transition(self):
        episode = lean_episode()
        first = episode["transitions"][0]
        first["evidence"].update(execution_outcome="timed_out", checker_outcome="not_run", task_success=None)
        first["observation"].update(execution_outcome="timed_out", checker_outcome="not_run", task_success=None)
        episode["transitions"] = [first]
        episode["final_candidate"] = first["action"]["candidate"]
        episode["final_artifact"] = assemble(
            TaskSpec.from_dict(episode["task"]), episode["final_candidate"],
        ).to_dict()
        episode["final_evidence"] = first["evidence"]
        with TemporaryDirectory() as tmp:
            root = Path(tmp)
            source = root / "episode.jsonl"
            jsonl(source, [episode])
            out = root / "export"
            result = export_training_data(out, episodes=[source])
            self.assertEqual({k: v for k, v in result["views"].items() if v}, {"grpo": 1, "trajectory": 1})
            trajectory, = read_jsonl(out / "trajectory.jsonl")
            self.assertIsNone(trajectory["reward"])
            self.assertEqual(trajectory["disposition"], "infrastructure_failure")
            self.assertEqual((trajectory["terminated"], trajectory["truncated"]), (False, True))

    @unittest.skipUnless((EVIDENCE / "conformance.json").is_file(), "requires repository evidence")
    def test_grpo_deduplicates_runtime_tasks_and_archived_prompts(self):
        episode = lean_episode()
        task = TaskSpec.from_dict(episode["task"])
        with TemporaryDirectory() as tmp:
            root = Path(tmp)
            source = root / "episode.jsonl"
            jsonl(source, [episode])
            lock = root / "local-lock.json"
            out = root / "export"
            with (patch("itpeval.learning.training_data.load_project") as load,
                  patch("itpeval.learning.training_data.build_task", return_value=task) as build):
                result = export_training_data(out, locks=[lock, lock], episodes=[source])
            load.assert_called_once_with(lock)
            build.assert_called_once_with(load.return_value, "completion.json")
            row, = read_jsonl(out / "grpo.jsonl")
            binding = result["runtime_tasks"][row["task_id"]]
            self.assertEqual(binding["lock_path"], str(lock))
            self.assertEqual(binding["environment_id"], row["environment_id"])
            self.assertEqual(result["views"]["sft"], 1)

    def test_pretraining_deduplicates_sources_and_excludes_exact_holdouts(self):
        with TemporaryDirectory() as tmp:
            root = Path(tmp)
            bundles = [root / "bundle-a", root / "bundle-b"]
            for bundle in bundles:
                native_source = store_blob(bundle / "blobs", b"same source")
                holdout = store_blob(bundle / "blobs", b"reserved source")
                failed = store_blob(bundle / "blobs", b"failed source")
                (bundle / "report.json").write_text(json.dumps({
                    "succeeded": ["A.lean", "held-out.lean"],
                    "sources": {"A.lean": native_source, "held-out.lean": holdout, "failed.lean": failed},
                    "prover": "lean4", "environment_id": "example",
                    "fields": {"proof_used_premises": "unavailable"},
                }), encoding="utf-8")
                for name in ("declarations", "contexts", "dependencies"):
                    (bundle / f"{name}.jsonl").touch()
            out = root / "export"
            result = export_training_data(out, bundles=bundles, split="train", exclude_source_hashes=[holdout])
            self.assertEqual(result["views"]["pretraining"], 1)
            source, = read_jsonl(out / "pretraining.jsonl")
            self.assertEqual(source["text"], "same source")
            self.assertEqual(source["split"], "train")
            self.assertEqual([origin["extraction_id"] for origin in source["origins"]], ["bundle-a", "bundle-b"])


if __name__ == "__main__":
    unittest.main()
