"""Read ordered visibility from expanded or compact extraction bundles."""

from heapq import merge
from itertools import chain
import json
from pathlib import Path

from itpeval.core.declarations import Context
from itpeval.corpus.storage import read_jsonl


METAMATH_PREFIX = "metamath-assertion-prefix-v1"


def _metadata(row):
    return {key: value for key, value in row.items() if key not in {"visible", "visibility"}}


class ContextTable:
    """Resolve logical contexts and test membership without expanding shared prefixes."""

    def __init__(self, bundle: Path):
        bundle = Path(bundle)
        self._path = bundle / "contexts.jsonl"
        self._rows = {}
        self._offsets = {}
        self._assertions = []
        self._assertion_positions = {}
        self._hypotheses = {}
        storage = set()
        scopes = {}
        offset = 0
        with self._path.open("rb") as stream:
            for line in stream:
                row = json.loads(line)
                context_id = row["context_id"]
                if context_id in self._rows:
                    raise ValueError(f"duplicate extraction context {context_id}")
                compact = "visibility" in row
                storage.add(compact)
                if compact:
                    if "visible" in row:
                        raise ValueError(f"conflicting visibility in context {context_id}")
                    self._offsets[context_id] = offset
                    # Keep the fields needed by membership queries. Full metadata
                    # such as disjointness conditions stays in the portable file.
                    scope = tuple(row["hypotheses"])
                    row = {key: row[key] for key in ("environment_id", "source_path", "visibility")}
                    row["hypotheses"] = scopes.setdefault(scope, scope)
                self._rows[context_id] = row
                offset += len(line)
        if len(storage) > 1:
            raise ValueError("an extraction bundle must use one context representation")
        self.compact = storage == {True}
        if self.compact:
            environments = {row["environment_id"] for row in self._rows.values()}
            if len(environments) != 1:
                raise ValueError("compact contexts must share a Metamath environment")
            names = set()
            referenced = set()
            for position, row in enumerate(read_jsonl(bundle / "declarations.jsonl")):
                if row["prover"] != "metamath" or row["environment_id"] not in environments:
                    raise ValueError("invalid declaration environment for compact contexts")
                if row["name"] in names:
                    raise ValueError(f"duplicate Metamath label {row['name']}")
                names.add(row["name"])
                context_id = row["context_id"]
                context = self._rows.get(context_id)
                if context is None or context["source_path"] != row["source_path"]:
                    raise ValueError(f"invalid Metamath context for {row['name']}")
                # Validate against only the declarations seen so far. A later
                # assertion or hypothesis must never become a retrieval input.
                count, _ = self._prefix(context_id)
                if count != len(self._assertions):
                    raise ValueError(f"Metamath assertion prefix differs at {row['name']}")
                referenced.add(context_id)
                member = (position, row["declaration_id"])
                if row["kind"] in {"$a", "$p"}:
                    self._assertions.append(member)
                    self._assertion_positions[member[1]] = len(self._assertions)
                elif row["kind"] in {"$f", "$e"}:
                    self._hypotheses[row["name"]] = member
                else:
                    raise ValueError(f"unexpected Metamath declaration kind {row['kind']}")
            if self._rows.keys() - referenced:
                raise ValueError("compact extraction contains an unreferenced context")
            previous_assertions = 0
            for context_id in self:
                count, _ = self._prefix(context_id)
                if count < previous_assertions:
                    raise ValueError("compact context prefixes must follow extraction order")
                previous_assertions = count

    def __iter__(self):
        return iter(self._rows)

    def __contains__(self, context_id):
        return context_id in self._rows

    def metadata(self, context_id) -> dict:
        """Read the recorded fields other than the visibility representation."""
        if not self.compact:
            return _metadata(self._rows[context_id])
        with self._path.open("rb") as stream:
            stream.seek(self._offsets[context_id])
            row = json.loads(stream.readline())
        if row["context_id"] != context_id:
            raise ValueError("extraction context file has changed")
        return _metadata(row)

    def metadata_rows(self):
        """Stream recorded context metadata in extraction order."""
        rows = read_jsonl(self._path) if self.compact else self._rows.values()
        yield from map(_metadata, rows)

    def environment_id(self, context_id) -> str:
        return self._rows[context_id]["environment_id"]

    def _prefix(self, context_id):
        row = self._rows[context_id]
        visibility = row["visibility"]
        if (not isinstance(visibility, dict) or visibility.get("kind") != METAMATH_PREFIX
                or set(visibility) != {"kind", "assertions"}
                or type(visibility["assertions"]) is not int
                or not 0 <= visibility["assertions"] <= len(self._assertions)):
            raise ValueError(f"invalid Metamath visibility in context {context_id}")
        try:
            hypotheses = [self._hypotheses[name] for name in row["hypotheses"]]
        except KeyError as exc:
            raise ValueError(f"unknown hypothesis in context {context_id}: {exc}") from exc
        if any(previous >= following for previous, following in zip(hypotheses, hypotheses[1:])):
            raise ValueError(f"hypotheses must follow extraction order in context {context_id}")
        return visibility["assertions"], hypotheses

    def visible_ids(self, context_id) -> list[str]:
        """Return the visible declaration IDs in source traversal order."""
        if not self.compact:
            return list(self._rows[context_id]["visible"])
        count, hypotheses = self._prefix(context_id)
        return [ident for _, ident in merge(self._assertions[:count], hypotheses)]

    def visible_subset(self, context_id, candidates) -> set[str]:
        """Find which supplied IDs are visible in the context."""
        if not self.compact:
            return set(candidates).intersection(self._rows[context_id]["visible"])
        count, hypotheses = self._prefix(context_id)
        active = {ident for _, ident in hypotheses}
        return {ident for ident in candidates if ident in active or self._assertion_positions.get(ident, count + 1) <= count}

    def context(self, context_id) -> Context:
        if not self.compact:
            return Context.from_dict(self._rows[context_id])
        return Context.from_dict({**self.metadata(context_id), "visible": self.visible_ids(context_id)})

    def _compact_changes(self):
        active = set()
        asserted = 0
        for context_id in self:
            count, hypotheses = self._prefix(context_id)
            visible = {ident for _, ident in hypotheses}
            additions = visible - active
            additions.update(ident for _, ident in self._assertions[asserted:count])
            asserted = count
            yield context_id, self.environment_id(context_id), additions, active - visible
            active = visible


def read_contexts(bundle: Path):
    """Yield the full Context records from either extraction representation."""
    table = ContextTable(bundle)
    for context_id in table:
        yield table.context(context_id)


def visibility_changes(bundle: Path):
    """Yield recorded contexts and their membership changes in extraction order."""
    rows = read_jsonl(Path(bundle) / "contexts.jsonl")
    first = next(rows, None)
    if first is None:
        return
    if "visibility" in first:
        rows.close()
        yield from ContextTable(bundle)._compact_changes()
        return
    active = set()
    for row in chain((first,), rows):
        visible = set(row["visible"])
        yield row["context_id"], row["environment_id"], visible - active, active - visible
        active = visible
