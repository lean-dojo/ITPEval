import json
import os
import shutil
import sqlite3
import tempfile
import unittest
from contextlib import closing
from pathlib import Path

from itpeval.alignment import Correspondence, SourceRef, reviewed_correspondences
from itpeval.corpus.contexts import ContextTable
from itpeval.corpus.datasets import partition_items
from itpeval.corpus.example import ENTRY, LIBRARY
from itpeval.corpus.storage import encode, jsonl, read_jsonl
from itpeval.environments import prepare_project
from itpeval.extraction import ExtractionError, extract_project
from itpeval.retrieval import CorpusIndex


class CorpusContractTests(unittest.TestCase):
    def test_partitions_keep_transitive_duplicates_and_programs(self):
        members = [{"theorem_id": 8}, {"theorem_id": 12}, {"theorem_id": 9, "split": "test"}]
        splits = partition_items(members, groups=[{8, 12}, {9, 12}])
        self.assertEqual({item["partition"] for item in splits.values()}, {"test"})
        self.assertEqual(splits, partition_items(members[::-1], groups=[[9, 12], [12, 8]]))
        with self.assertRaisesRegex(ValueError, "conflicting upstream"):
            partition_items([{**members[0], "split": "valid"}, *members[1:]], groups=[[8, 9]])

    def test_declaration_search_obeys_environment_and_visibility(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            jsonl(root / "contexts.jsonl", [
                {"context_id": "ctx", "environment_id": "env-a", "visible": ["x", "y"]}])
            jsonl(root / "declarations.jsonl", [
                {"declaration_id": k, "environment_id": "env-a", "name": n, "statement": s}
                for k, n, s in [("z", "future", "group"), ("y", "order", "group"),
                                ("x", "group", "some type")]])
            index = CorpusIndex.build(root)
            hits = index.search("GROUP", environment_id="env-a", context_id="ctx")
            self.assertEqual([r["declaration_id"] for r in hits], ["x", "y"])
            with self.assertRaises(ValueError):
                index.search("group", environment_id="env-b", context_id="ctx")

    def test_declaration_search_preserves_scope_changes_in_new_and_legacy_indexes(self):
        declarations = [
            {"declaration_id": key, "environment_id": env, "name": name, "statement": statement}
            for key, env, name, statement in [
                ("exact", "env-a", "Straße", "type"),
                ("prefix", "env-a", "Straßenbahn", "type"),
                ("statement", "env-a", "a", "mentions Straße"),
                ("other-project", "env-b", "Straße", "type"),
            ]
        ]
        contexts = [
            {"context_id": key, "environment_id": env, "visible": visible}
            for key, env, visible in [
                ("z", "env-a", ["statement", "exact", "prefix", "other-project", "exact"]),
                ("m", "env-a", ["prefix"]),
                ("b", "env-b", ["other-project", "exact"]),
                ("a", "env-a", []),
                ("n", "env-a", ["exact", "statement"]),
            ]
        ]
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            jsonl(root / "declarations.jsonl", declarations)
            jsonl(root / "contexts.jsonl", contexts)
            new = CorpusIndex.build(root)
            legacy = CorpusIndex(root / "legacy.sqlite")
            # Earlier extraction bundles used schema version zero and one row per visible pair.
            with closing(sqlite3.connect(legacy.path)) as db, db:
                db.executescript("""
                    CREATE TABLE declarations (id TEXT PRIMARY KEY, env TEXT, name TEXT, statement TEXT, record BLOB);
                    CREATE TABLE contexts (id TEXT PRIMARY KEY, env TEXT);
                    CREATE TABLE visible (context TEXT, decl TEXT, PRIMARY KEY (context,decl));
                """)
                db.executemany("INSERT INTO declarations VALUES (?,?,?,?,?)", (
                    (row["declaration_id"], row["environment_id"], row["name"].casefold(),
                     row["statement"].casefold(), encode(row)) for row in declarations
                ))
                db.executemany("INSERT INTO contexts VALUES (?,?)", (
                    (row["context_id"], row["environment_id"]) for row in contexts
                ))
                db.executemany("INSERT INTO visible VALUES (?,?)", (
                    (row["context_id"], decl) for row in contexts for decl in set(row["visible"])
                ))

            for index in (new, legacy):
                with self.subTest(index=index.path.name):
                    for row, expected in zip(contexts, [
                        ["exact", "prefix", "statement"], ["prefix"], ["other-project"], [], ["exact", "statement"],
                    ], strict=True):
                        hits = index.search("STRASSE", environment_id=row["environment_id"],
                                            context_id=row["context_id"])
                        self.assertEqual([hit["declaration_id"] for hit in hits], expected)
                        self.assertTrue(all(hit["visible_in"] == row["context_id"] for hit in hits))
                    self.assertEqual(index.search("", environment_id="env-a", context_id="z", limit=1)[0]["name"], "a")
                    self.assertEqual(index.search("", environment_id="env-a", context_id="z", limit=0), [])
                    with self.assertRaisesRegex(ValueError, "unknown context for environment"):
                        index.search("", environment_id="env-a", context_id="b")

    def test_source_locators_require_a_unique_identifier_in_code(self):
        from itpeval.corpus.importers import indexed_targets
        from itpeval.corpus.storage import digest

        member = {"source": "minif2f", "item_id": "valid/éxample", "theorem_id": 5}
        source = ('/- theorem éxample : False := by sorry /- nested -/ -/\n'
                  'theorem éxample : True := by trivial\n').encode()
        md = {"membership.json": "c" * 64}
        locate = lambda s: indexed_targets.locate(s, digest(s), member, "lean4", {"minif2f": {}},
                                                  "membership.json", md)
        item, = locate(source)
        self.assertEqual(item["basis"], "membership_identifier")
        self.assertEqual(source[item["start_byte"]:item["end_byte"]].decode(), "éxample")
        self.assertEqual(locate(source + source), [])
        self.assertTrue(indexed_targets.comment_only_metamath(b"$( only an @p statement, no native declaration $)"))
        self.assertFalse(indexed_targets.comment_only_metamath(b"$( header $) ax $a |- A $."))

    def test_review_is_versioned_and_keeps_unresolved_sources(self):
        source = SourceRef("absent.lean", None)
        target = SourceRef("proposition.lsp", "a" * 64)
        row = Correspondence("reviewed_formalization", "source_to_target", (source,), target, 75,
                             None, "review.json", "item", "b" * 64, "blocked_unfaithful_candidate", "passed", True)
        self.assertEqual(Correspondence.from_dict(row.to_dict()), row)
        self.assertEqual(row.native_check, "passed")
        self.assertEqual(row.decision, "blocked_unfaithful_candidate")


@unittest.skipUnless(os.getenv("ITPEVAL_TEST_NATIVE_EXTRACTION"), "requires native extraction toolchains")
class NativeIsolationTests(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        self.root = Path(self.tmp.name)
        self.prefix = Path(os.environ["ITPEVAL_PREFIX"])
        self.cache = Path(os.environ.get("ITPEVAL_TEST_CACHE", self.root / "cache"))

    def test_metamath_import_cache_identity_and_disjoint_variables(self):
        project = self.root / "mm"
        shutil.copytree(LIBRARY / "metamath/library", project)
        def prepare():
            return prepare_project("metamath", project, prefix=self.prefix, cache=self.cache)
        before = prepare()
        result = extract_project(before, ENTRY["metamath"], self.root / "out")
        (project / "base.mm").write_bytes((project / "base.mm").read_bytes() + b"\n$( revision $)\n")
        after = prepare()
        revised = extract_project(after, ENTRY["metamath"], self.root / "out")
        self.assertNotEqual(before.environment_id, after.environment_id)
        self.assertNotEqual(result.path, revised.path)
        (project / "client.mm").write_text("$[ base.mm $]\nwrong $p |- pair x x $= vx vx pair-dv $.\n")
        with self.assertRaises(ExtractionError) as caught:
            extract_project(prepare(), ENTRY["metamath"], self.root / "out")
        self.assertIn("disjoint", str(caught.exception).lower())
        failure = json.loads(caught.exception.report_path.read_bytes())
        self.assertEqual(failure["succeeded"], [])

    def test_metamath_compact_visibility_preserves_include_scope_and_evidence(self):
        project = self.root / "mm"
        project.mkdir()
        (project / "base.mm").write_text(
            "$c |- wff $.\n$v p $.\nwp $f wff p $.\nstep $a |- p $.\n"
            "${\n  local.h $e |- p $.\n  side $p |- p $= local.h $.\n"
            "  side.next $p |- p $= local.h $.\n$}\n"
            "after $p |- p $= wp step $.\n"
        )
        (project / "client.mm").write_text("$[ base.mm $]\nacross $p |- p $= wp step $.\n")
        prepared = prepare_project("metamath", project, prefix=self.prefix, cache=self.cache)
        expanded = extract_project(prepared, "client.mm", self.root / "out")
        compact = extract_project(prepared, "client.mm", self.root / "out", context_storage="compact")
        self.assertNotEqual(expanded.path, compact.path)
        self.assertEqual(expanded.report["structures"], compact.report["structures"])
        self.assertEqual((expanded.path / "dependencies.jsonl").read_bytes(),
                         (compact.path / "dependencies.jsonl").read_bytes())
        for key in expanded.report["structures"].values():
            path = Path("blobs") / key[:2] / key[2:]
            self.assertEqual((expanded.path / path).read_bytes(), (compact.path / path).read_bytes())

        full_contexts, compact_contexts = ContextTable(expanded.path), ContextTable(compact.path)
        expected = list(read_jsonl(expanded.path / "declarations.jsonl"))
        actual = list(read_jsonl(compact.path / "declarations.jsonl"))
        names = {row["declaration_id"]: row["name"] for row in actual}
        sequences = {}
        for old, new in zip(expected, actual, strict=True):
            self.assertEqual(old, {**new, "context_id": old["context_id"]})
            original = full_contexts.context(old["context_id"]).to_dict()
            resolved = compact_contexts.context(new["context_id"]).to_dict()
            self.assertEqual(original, {**resolved, "context_id": old["context_id"]})
            sequences[new["name"]] = [names[key] for key in resolved["visible"]]
        self.assertEqual(sequences["side.next"], ["wp", "step", "local.h", "side"])
        self.assertEqual(sequences["after"], ["wp", "step", "side", "side.next"])
        self.assertEqual(sequences["across"], ["wp", "step", "side", "side.next", "after"])

    def test_agda_rejects_unresolved_metas(self):
        project = self.root / "agda"
        project.mkdir()
        (project / "Hole.agda").write_text(
            "{-# OPTIONS --allow-unsolved-metas #-}\nmodule Hole where\n"
            "open import Agda.Builtin.Nat using (Nat)\nx : Nat\nx = {!!}\n")
        prepared = prepare_project("agda", project, prefix=self.prefix, cache=self.cache)
        with self.assertRaises(ExtractionError):
            extract_project(prepared, "Hole.agda", self.root / "out")

        inspect = prepare_project("agda", project, prefix=self.prefix, cache=self.cache,
                                  checking_profile="inspect_incomplete")
        bundle = extract_project(inspect, "Hole.agda", self.root / "out")
        key = bundle.report["structures"]["Hole.agda#interaction"]
        report = json.loads((bundle.path / "blobs" / key[:2] / key[2:]).read_bytes())
        self.assertEqual(report["goals"]["visibleGoals"][0]["type"], "Nat")
        self.assertIsInstance(report["constraints"], list)
        self.assertEqual([d["checking_status"] for d in read_jsonl(bundle.path / "declarations.jsonl")],
                         ["incomplete_module"])

    def test_rocq_native_aborted_proof_keeps_given_up_goal(self):
        project = self.root / "rocq"
        project.mkdir()
        (project / "Goals.v").write_text("Goal True. admit. Abort.\nLemma ok : True. Proof. exact I. Qed.\n")
        prepared = prepare_project("rocq", project, prefix=self.prefix, cache=self.cache)
        result = extract_project(prepared, "Goals.v", self.root / "out")
        key = result.report["structures"]["Goals.v#goals"]
        trace = json.loads((result.path / "blobs" / key[:2] / key[2:]).read_bytes())
        self.assertTrue(any("<goal>" in r["goals"]["given_up"] for r in trace if r["goals"]))
        self.assertEqual([r["name"] for r in read_jsonl(result.path / "declarations.jsonl")],
                         ["ITPProject.Goals.ok"])

    def test_rocq_admission_and_transitive_assumptions(self):
        project = self.root / "trust"
        project.mkdir()
        (project / "Trust.v").write_text("Axiom P : Prop. Lemma unfinished : P. Admitted.\n"
                                        "Lemma follows : P. Proof. exact unfinished. Qed.\n")
        prepared = prepare_project("rocq", project, prefix=self.prefix, cache=self.cache)
        result = extract_project(prepared, "Trust.v", self.root / "out")
        rows = {r["name"].split(".")[-1]: r for r in read_jsonl(result.path / "declarations.jsonl")}
        self.assertEqual(rows["unfinished"]["checking_status"], "assumption")
        self.assertEqual(rows["follows"]["checking_status"], "compiled_with_assumptions")

    def test_lean_options_and_transitive_admission(self):
        project = self.root / "lean"
        project.mkdir()
        (project / "Trust.lean").write_text(
            "theorem unfinished : True := by sorry\ntheorem follows : True := unfinished\n")
        checked = []
        for opts in ({}, {"pp.universes": "true"}):
            prepared = prepare_project("lean4", project, options=opts, prefix=self.prefix, cache=self.cache)
            result = extract_project(prepared, "Trust.lean", self.root / "out")
            rows = list(read_jsonl(result.path / "declarations.jsonl"))
            self.assertEqual({r["checking_status"] for r in rows}, {"admission_dependency"})
            checked.append(result.path)
        self.assertNotEqual(*checked)


@unittest.skipUnless(os.getenv("ITPEVAL_TEST_RELEASE_BUNDLE"), "requires imported release")
class FrozenImportTests(unittest.TestCase):
    def test_ten_prover_partitions_and_lossless_checksums(self):
        from collections import defaultdict

        from itpeval.backends.registry import prover_ids
        from itpeval.corpus.storage import digest

        root = Path(os.environ["ITPEVAL_TEST_RELEASE_BUNDLE"])
        manifest = json.loads((root / "manifest.json").read_bytes())

        def blob(key):
            data = (root / "blobs" / key[:2] / key[2:]).read_bytes()
            self.assertEqual(digest(data), key)
            return data

        members = {m["theorem_id"]: m for m in read_jsonl(root / "membership.jsonl")}
        proof_views, groups = defaultdict(set), defaultdict(set)
        for row in read_jsonl(root / "artifacts.jsonl"):
            item = members[row["theorem_id"]]
            self.assertEqual(row["partition"], item["partition"])
            self.assertEqual(row["group_id"], item["group_id"])
            self.assertEqual(row["checking_status"], "statement_only")
            self.assertEqual(row["artifact"], item["artifacts"][row["prover"]])
            if item["upstream_split"]:
                self.assertEqual(row["partition"], item["upstream_split"])
            if item["source"] == "ntp4vc":
                groups[item["program_source"]].add((row["group_id"], row["partition"]))
            raw = blob(row["source_blob"])
            if "target_locator_status" in row:
                for t in [*row["target_locators"], *row["candidate_target_locators"]]:
                    self.assertEqual(t["evidence_sha256"], row["source_blob"])
                    self.assertTrue(raw[t["start_byte"]:t["end_byte"]])
                    if t["basis"] != "individually_reviewed_span":
                        self.assertEqual(manifest["metadata_blobs"][t["authority_path"]], t["authority_sha256"])
                        if t["name"]:
                            self.assertEqual(raw[t["start_byte"]:t["end_byte"]].decode(), t["name"])
                    self.assertEqual(t["checking_status"], "statement_only")
                self.assertTrue(all(t["benchmark_role"] == "candidate_target_specification"
                                    for t in row["candidate_target_locators"]))
                if row["target_locator_status"] == "comment_only_no_declaration":
                    self.assertFalse(row["target_locators"] or row["candidate_target_locators"])
            proof_views[row["theorem_id"]].add(row["prover"])
        self.assertEqual(len(members), 2634)
        self.assertTrue(all(v == set(prover_ids()) for v in proof_views.values()))
        self.assertEqual(len(groups), 202)
        self.assertTrue(all(len(v) == 1 for v in groups.values()))
        for key in manifest["metadata_blobs"].values():
            blob(key)
        edges = list(read_jsonl(root / "reviewed_correspondences.jsonl"))
        self.assertEqual(len(edges), 2284)
        self.assertTrue(any(e["native_check"] == "passed" and e["decision"].startswith("blocked")
                            for e in edges))
        self.assertTrue(all(e["relation"] == "reviewed_formalization" for e in edges))
        subset = list(reviewed_correspondences(root, benchmark_item_id=392, decision="blocked_target_expressivity"))
        self.assertTrue(subset)
        self.assertTrue(all(e.target.content_sha256 is not None and e.evidence_source in manifest["metadata_blobs"]
                            for e in subset))
