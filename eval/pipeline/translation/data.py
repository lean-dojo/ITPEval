from __future__ import annotations

import hashlib
import json

from eval.pipeline.config import EXTENDED_STMTS_MANIFEST, PROOFS_JSON, PROVERS, STMTS_JSON


def load_statement_records(*, sources: list[str] | None = None) -> list[dict]:
    """Read the checksum-verified statement shards for all ten provers."""
    manifest = json.loads(EXTENDED_STMTS_MANIFEST.read_text(encoding="utf-8"))
    if manifest.get("schema_version") != "itpeval-extended-statements-v1":
        raise ValueError("unsupported extended statement manifest")
    records = []
    for source, entry in manifest["datasets"].items():
        if sources and source not in sources:
            continue
        path = EXTENDED_STMTS_MANIFEST.parent / entry["file"]
        payload = path.read_bytes()
        if hashlib.sha256(payload).hexdigest() != entry["sha256"]:
            raise ValueError(f"statement shard checksum mismatch: {source}")
        shard = json.loads(payload)
        if len(shard) != entry["records"] or any(r["source"] != source for r in shard):
            raise ValueError(f"statement shard inventory mismatch: {source}")
        records.extend(shard)
    return records


def load_pairs(
    mode: str = "stmts",
    *,
    sources: list[str] | None = None,
    tiers: list[str] | None = None,
    theorem_ids: list[int] | None = None,
    subset: set[tuple[str, int]] | None = None,
    corpus: str | None = None,
) -> list[dict]:
    """Load translation pairs from flat eval JSON.

    mode: 'stmts' or 'proofs'
    Returns list of dicts with keys: theorem_id, title, source, tier,
    src_prover, tgt_prover, src_content.
    """
    if mode not in {"stmts", "proofs"}:
        raise ValueError(f"unknown translation mode: {mode!r}")
    corpus = corpus or ("extended" if mode == "stmts" else "proofs")
    if corpus not in ({"extended", "published"} if mode == "stmts" else {"proofs"}):
        raise ValueError(f"corpus {corpus!r} is unavailable for {mode}")
    if mode == "proofs":
        records = json.loads(PROOFS_JSON.read_text(encoding="utf-8"))
    elif corpus == "published":
        records = json.loads(STMTS_JSON.read_bytes())
    else:
        records = load_statement_records(sources=sources)

    if sources:
        records = [r for r in records if r["source"] in sources]
    if tiers:
        records = [r for r in records if r["tier"] in tiers]
    if theorem_ids:
        records = [r for r in records if r["theorem_id"] in theorem_ids]
    if subset is not None:
        records = [r for r in records if (r["source"], int(r["theorem_id"])) in subset]

    # Pair records only within the same theorem/source group
    by_theorem: dict[tuple, list[dict]] = {}
    for r in records:
        if not r.get("content"):
            continue
        by_theorem.setdefault((r["source"], r["theorem_id"]), []).append(r)

    pairs = []
    for recs in by_theorem.values():
        prover_map = {r["prover"]: r for r in recs}
        if len(prover_map) != len(recs):
            raise ValueError("duplicate prover representation for one item")
        if not set(prover_map) <= set(PROVERS):
            raise ValueError("unknown prover in benchmark input")
        if corpus == "extended" and set(prover_map) != set(PROVERS):
            raise ValueError("statement item is not ten-way aligned")
        if corpus == "published" and set(prover_map) != {"lean4", "hol-light", "isabelle", "rocq"}:
            raise ValueError("the published statement population requires its four original provers")
        # For each theorem with n provers, emit all n * (n - 1) directed pairs
        for src_prover, src_rec in prover_map.items():
            for tgt_prover in prover_map:
                if src_prover != tgt_prover:
                    pairs.append({
                        "theorem_id":  src_rec["theorem_id"],
                        "title":       src_rec["title"],
                        "source":      src_rec["source"],
                        "tier":        src_rec["tier"],
                        "src_prover":  src_prover,
                        "tgt_prover":  tgt_prover,
                        "src_content": src_rec["content"],
                        "corpus": corpus,
                        "source_sha256": src_rec.get("sha256") or hashlib.sha256(
                            src_rec["content"].encode("utf-8")
                        ).hexdigest(),
                    })
    return pairs
