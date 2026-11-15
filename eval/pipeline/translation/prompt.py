from __future__ import annotations
from eval.pipeline.config import PROVER_DISPLAY, STATEMENT_TARGET_INSTRUCTIONS


def build_prompt(
    *,
    title: str,
    src_prover: str,
    tgt_prover: str,
    source_content: str,
    mode: str = "proofs",
) -> tuple[str, str]:
    """Return (system_prompt, user_prompt) for a translation task.

    mode='stmts': translate sorry-filled statement to target ITP (no proof).
    mode='proofs': translate full proof to target ITP.
    """

    src_name = PROVER_DISPLAY[src_prover]
    tgt_name = PROVER_DISPLAY[tgt_prover]

    # Statement mode asks for theorem files with admitted proofs; proof mode asks for full files
    if mode == "stmts":
        target_instruction = STATEMENT_TARGET_INSTRUCTIONS[tgt_prover]
        system = (
            f"You are an expert in interactive theorem proving, fluent in {src_name} and {tgt_name}. "
            f"Your task is to translate theorem statements from {src_name} to {tgt_name}. "
            f"Return only the complete {tgt_name} statement file, "
            f"with no explanation or markdown fencing. {target_instruction}"
        )
        user = (
            f"Translate the following {src_name} theorem statement of \"{title}\" into {tgt_name}. "
            f"Do not prove the theorem. {target_instruction}\n\n"
            f"=== {src_name} statement ===\n"
            f"{source_content.strip()}\n\n"
            f"=== {tgt_name} statement ==="
        )
    else:
        system = (
            f"You are an expert in interactive theorem proving, fluent in {src_name} and {tgt_name}. "
            f"Your task is to translate formal proofs from {src_name} to {tgt_name}. "
            f"Return only the complete {tgt_name} proof file contents, with no explanation or markdown fencing."
        )
        user = (
            f"Translate the following {src_name} proof of \"{title}\" into {tgt_name}.\n\n"
            f"=== {src_name} proof ===\n"
            f"{source_content.strip()}\n\n"
            f"=== {tgt_name} translation ==="
        )

    return system, user
