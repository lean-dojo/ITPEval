from __future__ import annotations

import hashlib
import json
import tempfile
import unittest
from collections import Counter, defaultdict
from itertools import permutations
from pathlib import Path
from unittest.mock import patch

from data.extended_inventory import EXPECTED, canonical_key
from eval.pipeline.config import PROVERS, REPO_ROOT, STMTS_JSON, PROOFS_JSON
from eval.pipeline.records import translation_record_key, translation_custom_id
from eval.pipeline.translation.data import load_pairs, load_statement_records


class ExtendedCorpusTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.records = load_statement_records()

    def test_exact_eight_dataset_ten_prover_population(self):
        self.assertEqual(Counter(r["source"] for r in self.records),
                         {source: count * 10 for source, count in EXPECTED.items()})
        grouped = defaultdict(list)
        for row in self.records:
            grouped[(row["source"], row["theorem_id"])].append(row["prover"])
        self.assertEqual(len(grouped), 2634)
        self.assertTrue(all(len(prs) == 10 and set(prs) == set(PROVERS) for prs in grouped.values()))

    def test_exported_source_bytes_and_hashes(self):
        for row in self.records:
            raw = (REPO_ROOT / row["artifact"]).read_bytes()
            self.assertEqual(row["content"].encode("utf-8"), raw, row["artifact"])
            self.assertEqual(row["sha256"], hashlib.sha256(raw).hexdigest())

    def test_overlapping_ids_keep_historical_meaning(self):
        frozen = json.loads((REPO_ROOT / "eval/subsets/full_stmts_390.json").read_text())
        old = {}
        for r in frozen:
            key = r["title"] if r["source"] != "minif2f" else r["split"] + "/" + r["title"]
            old[(r["source"], canonical_key(r["source"], key))] = r["theorem_id"]
        for r in self.records:
            identity = (r["source"], r["item_id"])
            if identity in old:
                self.assertEqual(r["theorem_id"], old[identity])
            else:
                self.assertGreater(r["theorem_id"], 390)

    def test_frozen_inputs_are_byte_identical_to_public_baseline(self):
        for path, expected in (
            (STMTS_JSON, "09363054e968092c2c18e576d32adf62e18a3f458ac81ac552489ad3d9fb10bc"),
            (PROOFS_JSON, "642901a9b4f0c2b8fc3c87567d2374808f981c6ecc7172ae953d9be7a4f17611"),
        ):
            self.assertEqual(hashlib.sha256(path.read_bytes()).hexdigest(), expected)

    def test_default_covers_every_prover_direction_equally(self):
        pairs = load_pairs()
        self.assertEqual(len(pairs), 237060)
        self.assertEqual(Counter((p["src_prover"], p["tgt_prover"]) for p in pairs),
                         {direction: 2634 for direction in permutations(PROVERS, 2)})
        self.assertEqual(len(load_pairs("proofs")), 888)

    def test_empty_subset_does_not_expand_to_full_population(self):
        self.assertEqual(load_pairs("stmts", sources=["babel-formal"], subset=set()), [])
        self.assertEqual(load_pairs("proofs", subset=set()), [])

    def test_rejects_unknown_translation_mode(self):
        with self.assertRaisesRegex(ValueError, "unknown translation mode"):
            load_pairs("unknown")

    def test_manifest_checksums_detect_corrupted_shards(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            (root / "sample.json").write_text("[]")
            (root / "manifest.json").write_text(json.dumps({
                "schema_version": "itpeval-extended-statements-v1",
                "datasets": {"sample": {"file": "sample.json", "records": 0, "sha256": "wrong"}},
            }))
            with patch("eval.pipeline.translation.data.EXTENDED_STMTS_MANIFEST", root / "manifest.json"):
                with self.assertRaisesRegex(ValueError, "checksum mismatch"):
                    load_statement_records()

    def test_extended_custom_ids_do_not_reuse_historical_checkpoints(self):
        pair = {"source": "babel-formal", "theorem_id": 1,
                "src_prover": "lean4", "tgt_prover": "rocq", "source_sha256": "a" * 64}
        legacy = "babel-formal__1__lean4__rocq__sample0"
        self.assertEqual(translation_custom_id(pair), legacy)
        extended = {**pair, "corpus": "extended"}
        self.assertNotEqual(translation_custom_id(extended), legacy)
        self.assertNotEqual(translation_custom_id(extended),
                            translation_custom_id({**extended, "source_sha256": "b" * 64}))

    def test_extended_checkpoint_keys_separate_models_and_sampling(self):
        row = {"corpus": "extended", "custom_id": "fixture", "model": "one", "temperature": 0}
        self.assertNotEqual(translation_record_key(row),
                            translation_record_key({**row, "model": "two"}))
        self.assertNotEqual(translation_record_key(row),
                            translation_record_key({**row, "temperature": 1}))

    def test_extended_request_ids_are_compact(self):
        identity = translation_custom_id({
            "corpus": "extended", "source": "thousand-theorems", "theorem_id": 2654,
            "src_prover": "hol-light", "tgt_prover": "isabelle", "source_sha256": "f" * 64,
        }, sample_idx=4)
        self.assertLessEqual(len(identity), 64)
        self.assertRegex(identity, r"^ext1_[0-9a-f]+$")

    def test_historical_checkpoint_keys_are_unchanged(self):
        self.assertEqual(translation_record_key({"custom_id": "old-id"}), "old-id")
        self.assertEqual(translation_record_key({"corpus": "proofs", "custom_id": "old-id"}), "old-id")


if __name__ == "__main__":
    unittest.main()
