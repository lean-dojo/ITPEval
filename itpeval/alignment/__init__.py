"""Evidence-bearing correspondences between versioned source artifacts."""

from dataclasses import dataclass

from itpeval.core.records import Record


@dataclass(frozen=True)
class SourceRef(Record):
    path: str
    content_sha256: str | None


@dataclass(frozen=True)
class Correspondence(Record):
    relation: str
    direction: str
    sources: tuple[SourceRef, ...]
    target: SourceRef
    benchmark_item_id: int | None
    assumptions: tuple[str, ...] | None
    evidence_source: str
    evidence_key: str
    evidence_sha256: str
    decision: str
    native_check: str | None
    source_matches_review: bool


def reviewed_correspondences(bundle, *, benchmark_item_id=None, target_path=None, decision=None):
    """Stream directed, versioned review decisions from an imported ITPEval release."""
    from pathlib import Path

    from itpeval.corpus.storage import read_jsonl

    for row in read_jsonl(Path(bundle) / "reviewed_correspondences.jsonl"):
        if benchmark_item_id is not None and row["benchmark_item_id"] != benchmark_item_id:
            continue
        if target_path is not None and row["target"]["path"] != target_path:
            continue
        if decision is None or row["decision"] == decision:
            yield Correspondence.from_dict(row)
