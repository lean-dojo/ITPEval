import json
import tempfile
import unittest
from pathlib import Path

from itpeval.corpus.benchmark_training import export_benchmark
from itpeval.corpus.storage import encode, jsonl, read_jsonl, store_blob


class BenchmarkTrainingTests(unittest.TestCase):
    def test_reference_export_preserves_splits_and_evidence(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            corpus = root / "archive"
            corpus.mkdir()

            def blob(text):
                return store_blob(corpus / "blobs", text.encode("utf-8"))

            def archived(row, prover, text):
                sha = blob(text)
                return {**row, "prover": prover, "artifact": row["artifacts"][prover],
                        "sha256": sha, "source_blob": sha, "target_locator_status": "released_identifier"}

            members = [
                {"source": "babel-formal", "theorem_id": 1, "group_id": 1, "partition": "train",
                 "item_id": "item", "artifacts": {"lean4": "item.lean", "rocq": "item.v", "pvs": "item.pvs"}},
                {"source": "ntp4vc", "theorem_id": 2, "group_id": 2, "partition": "train",
                 "item_id": "pearl/obligation", "artifacts": {"lean4": "vc.lean", "rocq": "vc.v"}},
            ]
            train, test = members
            source = archived(train, "lean4", "theorem one")
            target = archived(train, "rocq", "Theorem one.")
            blocked = archived(train, "pvs", "unsuitable statement")
            articles = [source, target, blocked, archived(test, "lean4", "theorem one"),
                        archived(test, "rocq", "Theorem vc.")]

            evidence_path = "corpus-extension/semantic_canonical_resolutions.json"
            decisions = {
                "accept": {"candidate_path": target["artifact"], "candidate_sha256": target["sha256"],
                           "decision": "accept_manual_repair", "native_check": "passed",
                           "source_authority": [source["artifact"]]},
                "block": {"candidate_path": blocked["artifact"], "candidate_sha256": blocked["sha256"],
                          "decision": "blocked_target_expressivity", "native_check": "passed",
                          "source_authority": [source["artifact"]]},
            }
            sha = blob(json.dumps({"resolutions": decisions}))
            metadata = {
                evidence_path: sha,
                "LICENSE": blob("license notice"),
                "eval/data/proofs.json": blob("[]"),
                "eval/data/minif2f_nl4itp.jsonl": blob(""),
                "data/ntp4vc/data/test_set.lean.txt.lst": blob("data/why3/pearl/native_vcg/lean/obligation.lean"),
            }
            (corpus / "manifest.json").write_bytes(
                encode({"metadata_blobs": metadata, "items": 2, "artifacts": 5, "release_source_commit": "test"})
            )
            jsonl(corpus / "membership.jsonl", members)
            jsonl(corpus / "artifacts.jsonl", articles)
            jsonl(corpus / "reviewed_correspondences.jsonl", [
                {"decision": decision["decision"], "native_check": "passed", "source_matches_review": True,
                 "evidence_source": evidence_path, "evidence_sha256": sha, "evidence_key": key,
                 "target": {"path": decision["candidate_path"], "content_sha256": decision["candidate_sha256"]},
                 "sources": [{"path": source["artifact"], "content_sha256": source["sha256"]}]}
                for key, decision in decisions.items()
            ])
            output = root / "reference"
            with self.assertRaisesRegex(ValueError, "evaluation data"):
                export_benchmark(corpus, output)
            self.assertFalse(output.exists())
            report = export_benchmark(corpus, output, include_benchmark_references=True, style="chat")
            self.assertEqual(report["excluded_hashes_in_multiple_partitions"], 1)
            self.assertEqual(report["views"]["statement_translation_reviewed"], {})
            self.assertEqual(report["views"]["statement_translation_reference"], {})
            test_row, = read_jsonl(output / "pretraining_reference/test.jsonl")
            self.assertEqual(test_row["source"], "ntp4vc")
            self.assertEqual(test_row["release_partition"], "train")
            self.assertEqual(test_row["upstream_split"], "test")
            self.assertTrue(test_row["reference_only"])
            self.assertEqual((output / "notices/LICENSE").read_text(), "license notice")

            # Replacing the coincident test source restores its two directions.
            # The accepted review applies only to its original ordered pair.
            articles[3] = archived(test, "lean4", "theorem vc")
            jsonl(corpus / "artifacts.jsonl", articles)
            output = root / "without-conflict"
            report = export_benchmark(corpus, output, include_benchmark_references=True, style="chat")
            self.assertEqual(report["views"]["statement_translation_reference"], {"train": 2, "test": 2})
            reviewed, = read_jsonl(output / "statement_translation_reviewed/train.jsonl")
            self.assertEqual(reviewed["target_native_check"], "passed")
            self.assertEqual(reviewed["review_evidence_sha256"], sha)
            self.assertEqual(reviewed["prompt"][0]["role"], "user")
            self.assertEqual(reviewed["completion"], [{"role": "assistant", "content": "Theorem one."}])


if __name__ == "__main__":
    unittest.main()
