"""Export the version-one declaration and premise-selection views to Parquet."""
from __future__ import annotations

import argparse
import os
import tempfile
from itertools import islice
from pathlib import Path

from .storage import read_jsonl


def _schema(pa, view):
    text = pa.string()
    ids = pa.list_(text)
    version = ("schema_version", pa.int32())
    identity = [(field, text) for field in
                ("declaration_id", "environment_id", "prover", "name", "kind", "statement", "context_id")]
    if view == "declarations":
        return pa.schema([version, *identity, ("source_path", text), ("source_hash", text),
                          ("start_byte", pa.int64()), ("end_byte", pa.int64()),
                          ("checking_status", text), ("evidence", ids)])
    if view == "premises":
        edge = pa.struct([version, *[(k, text) for k in ("origin", "relation", "target_name", "target_id")]])
        return pa.schema([version, ("task_id", text), ("operation", text), ("declaration", pa.struct(identity)),
                          ("available", ids), ("retrieved", ids), ("proof_used", pa.list_(edge)),
                          ("proof_used_availability", text)])
    raise ValueError("view must be declarations or premises")


def export_parquet(source: Path, destination: Path, *, view: str, batch_size: int = 4096) -> int:
    """Return the number of rows written, preserving nested records and nulls."""
    import pyarrow as pa

    return write_rows_parquet(source, destination, _schema(pa, view), batch_size=batch_size)


def write_rows_parquet(source: Path, destination: Path, schema, *, batch_size: int = 4096) -> int:
    """Convert versioned JSONL to an explicit Parquet schema in bounded batches."""
    import pyarrow as pa
    import pyarrow.parquet as pq

    if batch_size < 1:
        raise ValueError("batch_size must be positive")
    source, destination = Path(source), Path(destination)
    if source.resolve() == destination.resolve():
        raise ValueError("select an output distinct from the JSONL source")
    destination.parent.mkdir(parents=True, exist_ok=True)
    with tempfile.TemporaryDirectory(dir=destination.parent) as temp:
        stage = Path(temp) / "rows.parquet"
        total = 0
        with pq.ParquetWriter(stage, schema, compression="zstd") as writer:
            rows = iter(read_jsonl(source))
            while batch := list(islice(rows, batch_size)):
                if any(row.get("schema_version") != 1 for row in batch):
                    raise ValueError("expected schema-version-one records")
                table = pa.Table.from_pylist(batch, schema=schema)
                # Arrow can ignore extra fields when given an explicit schema.
                # Refuse a lossy conversion, including nested schema changes.
                if table.to_pylist() != batch:
                    raise ValueError("input rows differ from the Parquet schema")
                writer.write_table(table)
                total += len(batch)
        os.replace(stage, destination)
    return total


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("view", choices=("declarations", "premises"))
    parser.add_argument("source", type=Path)
    parser.add_argument("destination", type=Path)
    args = parser.parse_args()
    print(export_parquet(args.source, args.destination, view=args.view))
