from pathlib import Path
from tempfile import TemporaryDirectory
import unittest

from itpeval.core.declarations import Context, DependencyEdge, FormalObject
from itpeval.corpus.contexts import ContextTable, METAMATH_PREFIX, read_contexts
from itpeval.corpus.datasets import premise_rows
from itpeval.corpus.storage import jsonl, read_jsonl
from itpeval.environments.cache import write_json
from itpeval.retrieval import CorpusIndex


def write_bundle(path, compact):
    path.mkdir()
    definitions = [
        ("f", "$f", 0, (), ()),
        ("a", "$a", 0, ("f",), ("f",)),
        ("e", "$e", 1, ("f",), ("f", "a")),
        ("p", "$p", 1, ("f", "e"), ("f", "a", "e")),
        ("outside", "$a", 2, (), ("a", "p")),
    ]
    declarations, contexts = [], []
    for index, (name, kind, count, hypotheses, visible) in enumerate(definitions):
        context_id = f"context-{name}"
        declaration = FormalObject(name, "env", "metamath", name, kind, "test statement", "base.mm",
                                   "hash", index, index + 1, context_id, "proof_verified")
        context = Context(context_id, "env", "base.mm", visible, hypotheses=hypotheses).to_dict()
        if compact:
            del context["visible"]
            context["visibility"] = {"kind": METAMATH_PREFIX, "assertions": count}
        declarations.append(declaration.to_dict())
        contexts.append(context)
    jsonl(path / "declarations.jsonl", declarations)
    jsonl(path / "contexts.jsonl", contexts)
    jsonl(path / "dependencies.jsonl", [DependencyEdge("p", "proof_used_premise", "a", "a").to_dict()])
    write_json(path / "report.json", {"entrypoint": "base.mm", "fields": {"proof_used_premises": "observed"}})


class CompactContextTests(unittest.TestCase):
    def test_logical_contexts_and_rankings_match_expanded_output(self):
        with TemporaryDirectory() as directory:
            expanded, compact = (Path(directory) / mode for mode in ("expanded", "compact"))
            write_bundle(expanded, False)
            write_bundle(compact, True)
            self.assertEqual(list(read_contexts(expanded)), list(read_contexts(compact)))
            table = ContextTable(compact)
            self.assertEqual(table.visible_subset("context-outside", ("f", "a", "p", "missing")), {"a", "p"})
            full_index, small_index = CorpusIndex.build(expanded), CorpusIndex.build(compact)
            for context in read_contexts(compact):
                query = {"environment_id": "env", "context_id": context.context_id}
                self.assertEqual(full_index.search("statement", **query), small_index.search("statement", **query))
            self.assertEqual(list(premise_rows(expanded)), list(premise_rows(compact)))
            for row in premise_rows(compact, visibility="reference"):
                self.assertIsNone(row["available"])
                self.assertIn(row["declaration"]["context_id"], table)

    def test_future_declarations_cannot_enter_retrieval_context(self):
        with TemporaryDirectory() as directory:
            compact = Path(directory) / "compact"
            write_bundle(compact, True)
            path = compact / "contexts.jsonl"
            rows = list(read_jsonl(path))
            rows[0]["visibility"]["assertions"] = 1
            jsonl(path, rows)
            with self.assertRaisesRegex(ValueError, "invalid Metamath visibility"):
                ContextTable(compact)
