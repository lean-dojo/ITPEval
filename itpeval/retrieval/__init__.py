"""Exact, reproducible name and statement lookup restricted to a recorded context."""

import json
import sqlite3
from contextlib import closing
from pathlib import Path
from typing import Protocol

from itpeval.corpus.contexts import visibility_changes
from itpeval.corpus.storage import encode, read_jsonl

_RANGE_SCHEMA_VERSION = 1


class Retriever(Protocol):
    def search(self, text: str, *, environment_id: str, context_id: str, limit: int = 20) -> list[dict]: ...


class CorpusIndex:
    """Search declarations visible at a target in one recorded project environment."""

    def __init__(self, path):
        self.path = Path(path)

    @classmethod
    def build(cls, bundle):
        bundle = Path(bundle)
        with closing(sqlite3.connect(bundle / "index.sqlite")) as db, db:
            db.executescript("""
                CREATE TABLE declarations (id TEXT PRIMARY KEY, env TEXT, name TEXT, statement TEXT, record BLOB);
                CREATE TABLE contexts (id TEXT PRIMARY KEY, env TEXT, position INTEGER NOT NULL);
                CREATE TABLE visibility_ranges (
                    decl TEXT, first_position INTEGER, stop_position INTEGER NOT NULL,
                    PRIMARY KEY (decl,first_position)
                ) WITHOUT ROWID;
            """)
            for row in read_jsonl(bundle / "declarations.jsonl"):
                db.execute("INSERT INTO declarations VALUES (?,?,?,?,?)",
                           (row["declaration_id"], row["environment_id"], row["name"].casefold(),
                            row["statement"].casefold(), encode(row)))
            # A declaration can leave scope and reappear. Store one range per consecutive appearance.
            active = {}
            context_count = 0
            for position, (context, environment, added, removed) in enumerate(visibility_changes(bundle)):
                context_count = position + 1
                db.execute("INSERT INTO contexts VALUES (?,?,?)", (context, environment, position))
                db.executemany("INSERT INTO visibility_ranges VALUES (?,?,?)",
                               ((decl, active.pop(decl), position) for decl in sorted(removed)))
                for decl in added:
                    active[decl] = position
            db.executemany("INSERT INTO visibility_ranges VALUES (?,?,?)",
                           ((decl, first, context_count) for decl, first in sorted(active.items())))
            db.execute("CREATE INDEX visibility_ranges_by_start ON visibility_ranges(first_position,stop_position)")
            db.execute(f"PRAGMA user_version = {_RANGE_SCHEMA_VERSION}")
        return cls(bundle / "index.sqlite")

    def search(self, text: str, *, environment_id: str, context_id: str, limit: int = 20):
        if limit < 0:
            raise ValueError("limit must be nonnegative")
        term = text.casefold()
        with closing(sqlite3.connect(self.path.resolve().as_uri() + "?mode=ro", uri=True)) as db:
            version, = db.execute("PRAGMA user_version").fetchone()
            if version == 0:
                context_column = "id"
                table = "visible"
                restriction = "v.context = :context"
            elif version == _RANGE_SCHEMA_VERSION:
                context_column = "position"
                table = "visibility_ranges"
                restriction = "v.first_position <= :context AND v.stop_position > :context"
            else:
                raise ValueError(f"unsupported corpus index version {version}")

            context = db.execute(f"SELECT {context_column} FROM contexts WHERE id=? AND env=?",
                                 (context_id, environment_id)).fetchone()
            if context is None:
                raise ValueError("unknown context for environment")
            rows = db.execute(f"""
                SELECT d.record FROM {table} v JOIN declarations d ON d.id = v.decl
                 WHERE {restriction} AND d.env=:environment AND (instr(d.name,:term) OR instr(d.statement,:term))
                 ORDER BY (d.name=:term) DESC, (instr(d.name,:term)>0) DESC, d.name, d.id LIMIT :limit
            """, {"context": context[0], "environment": environment_id, "term": term, "limit": limit})
            return [{**json.loads(record), "visible_in": context_id} for record, in rows]
