"""Regression cases for published result files the installed release gate consumes."""
import json
import shutil
import tempfile
import unittest
from pathlib import Path

from scripts.check_release import check


ROOT = Path(__file__).resolve().parents[2] / "benchmarks/runtime"


class ReleaseEvidenceTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)
        self.evidence = self.root / "evidence/metamath"
        shutil.copytree(ROOT / "evidence/metamath", self.evidence)
        self.report = self.root / "qualification.jsonl"
        rows = [line for line in (ROOT / self.report.name).read_text().splitlines()
                if json.loads(line)["prover"] == "metamath"]
        self.report.write_text("\n".join(rows) + "\n")

    def validate(self):
        check([self.report], ["metamath"])

    def test_published_shard_passes(self):
        self.validate()

    def test_missing_native_probe_fails(self):
        rows = [line for line in self.report.read_text().splitlines()
                if json.loads(line)["operation"] != "replay_stack"]
        self.report.write_text("\n".join(rows))
        with self.assertRaisesRegex(ValueError, "replay_stack"):
            self.validate()

    def test_stale_markers_do_not_qualify_a_different_distribution(self):
        path = self.evidence / "smoke.json"
        data = json.loads(path.read_bytes())
        data["wheel_sha256"] = "0" * 64
        path.write_text(json.dumps(data))
        with self.assertRaisesRegex(ValueError, "installed CLI receipt"):
            self.validate()

    def test_unverified_trainer_evidence_fails_even_when_reward_matches(self):
        path = self.evidence / "evaluation.json"
        data = json.loads(path.read_bytes())
        data["valid"]["native_evidence"]["trainer"]["target_preservation"] = "unchecked"
        path.write_text(json.dumps(data))
        with self.assertRaises(ValueError):
            self.validate()

    def test_missing_replay_action_fails(self):
        record = json.loads((self.evidence / "conformance.json").read_bytes())
        path = self.evidence / record["replay"]
        data = json.loads(path.read_bytes())
        data["transitions"].pop(0)
        path.write_text(json.dumps(data))
        with self.assertRaisesRegex(ValueError, "number of transitions"):
            self.validate()
