"""Exercise mixed-prover exports and the provenance of shared declarations."""

import importlib.util
import json
from pathlib import Path
from tempfile import TemporaryDirectory
import unittest

from itpeval.core.declarations import Context, DependencyEdge, FormalObject
from itpeval.corpus.library_collection import export_collection, load_catalog
from itpeval.corpus.storage import jsonl, read_jsonl


def make_bundle(root, name, *, prover="future-prover", context="different-context",
                labels="unavailable", row_environment="matching-environment"):
    bundle = root / name
    bundle.mkdir()
    environment = "matching-environment"
    declaration = FormalObject("shared-declaration", row_environment, prover, "example", "theorem",
                               "P", "source", "source-hash", 0, 1, context, "kernel_checked")
    jsonl(bundle / "declarations.jsonl", (declaration.to_dict(),))
    jsonl(bundle / "contexts.jsonl", (Context(context, environment, "source", (context,)).to_dict(),))
    dependencies = [DependencyEdge(declaration.declaration_id, "proof_used_premise", "home", context).to_dict()]
    jsonl(bundle / "dependencies.jsonl", dependencies if labels == "observed" else ())
    (bundle / "report.json").write_text(json.dumps({
        "schema_version": 1, "prover": prover, "environment_id": environment,
        "entrypoint": name, "declarations": 1, "extractor_revision": {}, "project_inputs": {},
        "fields": {"proof_used_premises": labels}, "succeeded": ["source"], "skipped": [],
        "failed": [],
    }), encoding="utf-8")
    return bundle


def write_catalog(root, entries):
    path = root / "catalog.json"
    path.write_text(json.dumps({"schema_version": 1, "libraries": entries}), encoding="utf-8")
    return path


class LibraryCollectionTest(unittest.TestCase):
    def test_mixed_libraries_preserve_distinct_observations(self):
        with TemporaryDirectory() as tmp:
            root = Path(tmp)
            entries = [
                {"name": "New mathematics", "revision": "v1", "license": "MIT", "bundles": ["a", "b"]},
                {"name": "Other mathematics", "bundles": ["c"]},
            ]
            first = make_bundle(root, "a", context="visible-a", labels="observed")
            second = make_bundle(root, "b", context="visible-b")
            make_bundle(root, "c", prover="lean4", context="visible-c")
            catalog = write_catalog(root, entries)
            self.assertEqual(load_catalog(catalog)[0].bundles, (first.resolve(), second.resolve()))
            output = root / "combined"
            parquet = bool(importlib.util.find_spec("pyarrow"))
            result = export_collection(catalog, output, format="both" if parquet else "jsonl")
            self.assertEqual(result["counts"], {"declarations": 3, "premises": 3})
            self.assertEqual(result["libraries"][0]["successful_source_units"], 1)
            self.assertEqual(result["libraries"][0]["license"], "MIT")
            declarations = list(read_jsonl(output / "declarations.jsonl"))
            self.assertEqual([item["prover"] for item in declarations], ["future-prover", "future-prover", "lean4"])
            self.assertEqual([item["library_revision"] for item in declarations], ["v1", "v1", None])
            self.assertEqual(len({item["bundle_id"] for item in declarations}), 3)
            premises = list(read_jsonl(output / "premises.jsonl"))
            self.assertEqual(len({item["task_id"] for item in premises}), 3)
            self.assertEqual([item["available"] for item in premises], [["visible-a"], ["visible-b"], ["visible-c"]])
            self.assertEqual([item["proof_used_availability"] for item in premises],
                             ["observed", "unavailable", "unavailable"])
            if parquet:
                import pyarrow.parquet as pq

                self.assertEqual(pq.read_table(output / "declarations.parquet").to_pylist(), declarations)
                self.assertEqual(pq.read_table(output / "premises.parquet").to_pylist(), premises)

    def test_mismatched_environment_leaves_output_uncreated(self):
        with TemporaryDirectory() as tmp:
            root = Path(tmp)
            make_bundle(root, "example", row_environment="other")
            catalog = write_catalog(root, [{"name": "Library", "bundles": ["example"]}])
            output = root / "combined"
            with self.assertRaisesRegex(ValueError, "invalid declaration provenance"):
                export_collection(catalog, output)
            self.assertFalse(output.exists())

    def test_alias_paths_cannot_duplicate_one_bundle(self):
        with TemporaryDirectory() as tmp:
            root = Path(tmp)
            make_bundle(root, "example")
            catalog = write_catalog(root, [{"name": "Library", "bundles": ["example", "./example"]}])
            with self.assertRaisesRegex(ValueError, "duplicate bundle path"):
                load_catalog(catalog)
