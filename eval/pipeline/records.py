from __future__ import annotations

import hashlib
import json
from typing import Any


def translation_custom_id(pair: dict[str, Any], *, sample_idx: int = 0) -> str:
    # This ID is shared by sync runs, batch runs, checkpoints, and BEq outputs
    if pair.get("corpus") == "extended":
        identity = [pair["source"], pair["theorem_id"], pair["src_prover"],
                    pair["tgt_prover"], sample_idx, pair["source_sha256"]]
        digest = hashlib.sha256(json.dumps(identity, separators=(",", ":")).encode()).hexdigest()
        # Keep provider request IDs compact even for long dataset/prover names.
        return "ext1_" + digest[:40]
    return (
        f"{pair['source']}__{pair['theorem_id']}__"
        f"{pair['src_prover']}__{pair['tgt_prover']}__sample{sample_idx}"
    )


def translation_record_key(record: dict[str, Any]) -> str:
    custom_id = record.get("custom_id")
    if record.get("task_id") or record.get("result_schema") == "itpeval-translation-v2":
        schema = "itpeval-task-v1" if record.get("task_id") else record["result_schema"]
        return json.dumps([schema, record.get("task_id"), custom_id,
                           record.get("model"), record.get("model_id"), record.get("mode"),
                           record.get("temperature"), record.get("sample_idx", 0)], ensure_ascii=False)
    if record.get("corpus") == "extended":
        # New-corpus checkpoints distinguish model/sampling conditions. Keep
        # the historical branch below unchanged for existing results and BEq.
        return json.dumps({
            "custom_id": custom_id,
            "model": record.get("model"),
            "model_id": record.get("model_id"),
            "mode": record.get("mode"),
            "temperature": record.get("temperature", 0.0),
        }, sort_keys=True)
    if isinstance(custom_id, str) and custom_id:
        return custom_id
    # Older result files may not have custom_id; keep resume behavior stable
    return json.dumps(
        {
            "source": record.get("source"),
            "theorem_id": record.get("theorem_id"),
            "title": record.get("title"),
            "src_prover": record.get("src_prover"),
            "tgt_prover": record.get("tgt_prover"),
            "model": record.get("model"),
            "mode": record.get("mode"),
            "sample_idx": record.get("sample_idx", 0),
            "temperature": record.get("temperature"),
        },
        sort_keys=True,
        ensure_ascii=False,
    )


def translation_record_label(record: dict[str, Any]) -> str:
    custom_id = record.get("custom_id")
    if isinstance(custom_id, str) and custom_id:
        return custom_id
    return (
        f"{record.get('model', '?')} "
        f"{record.get('title', record.get('theorem_id', '?'))} "
        f"{record.get('src_prover', '?')}->{record.get('tgt_prover', '?')}"
    )


def make_translation_record(
    *,
    pair: dict[str, Any],
    model_cfg: dict[str, Any],
    mode: str,
    generated: str = "",
    verified: bool = False,
    translate_error: str = "",
    verify_error: str = "",
    translate_ms: int = 0,
    verify_ms: int = 0,
    sample_idx: int = 0,
    temperature: float = 0.0,
    custom_id: str | None = None,
) -> dict[str, Any]:
    cid = custom_id or translation_custom_id(pair, sample_idx=sample_idx)
    # Keep sync, batch, and post-hoc verification outputs on the same schema
    return {
        "result_schema": "itpeval-translation-v2",
        "task_success": None,
        "evidence": None,
        "custom_id": cid,
        "theorem_id": pair["theorem_id"],
        "title": pair["title"],
        "source": pair["source"],
        "tier": pair["tier"],
        "src_prover": pair["src_prover"],
        "tgt_prover": pair["tgt_prover"],
        "model": model_cfg["label"],
        "model_id": model_cfg["id"],
        "mode": mode,
        "sample_idx": sample_idx,
        "temperature": temperature,
        "generated": generated,
        "verified": verified,
        "translate_error": translate_error,
        "verify_error": verify_error,
        "translate_ms": translate_ms,
        "verify_ms": verify_ms,
        "corpus": pair.get("corpus"),
        "source_sha256": pair.get("source_sha256"),
    }
