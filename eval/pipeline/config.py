from __future__ import annotations
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parents[2]
EVAL_DIR = REPO_ROOT / "eval"

STMTS_JSON  = EVAL_DIR / "data" / "stmts.json"
PROOFS_JSON = EVAL_DIR / "data" / "proofs.json"
RESULTS_DIR       = EVAL_DIR / "results"
GENERATED_DIR     = RESULTS_DIR / "generated"
VERIFIED_DIR      = RESULTS_DIR / "verified"
BATCH_JOBS_DIR = RESULTS_DIR / "batch_jobs"

PROVERS = (
    "lean4",
    "rocq",
    "isabelle",
    "hol-light",
    "acl2",
    "agda",
    "hol4",
    "metamath",
    "mizar",
    "pvs",
)

PROVER_DISPLAY = {
    "lean4":     "Lean 4",
    "rocq":      "Rocq (Coq)",
    "isabelle":  "Isabelle/HOL",
    "hol-light": "HOL Light",
    "acl2":      "ACL2",
    "agda":      "Agda",
    "hol4":      "HOL4",
    "metamath":  "Metamath",
    "mizar":     "Mizar",
    "pvs":       "PVS",
}

PROVER_EXTENSIONS = {
    "lean4": ".lean",
    "rocq": ".v",
    "isabelle": ".thy",
    "hol-light": ".ml",
    "acl2": ".lsp",
    "agda": ".agda",
    "hol4": ".sml",
    "metamath": ".mm",
    "mizar": ".miz",
    "pvs": ".pvs",
}

SOURCE_FILENAMES = {
    "lean4": "source.lean",
    "rocq": "source.v",
    "isabelle": "Source.thy",
    "hol-light": "source.ml",
    "acl2": "source.lsp",
    "agda": "Source.agda",
    "hol4": "source.sml",
    "metamath": "source.mm",
    "mizar": "source.miz",
    "pvs": "source.pvs",
}

TARGET_FILENAMES = {
    "lean4": "Hello.lean",
    "rocq": "hello.v",
    "isabelle": "AgentTarget.thy",
    "hol-light": "hello.ml",
    "acl2": "AgentTarget.lsp",
    "agda": "AgentTarget.agda",
    "hol4": "AgentTarget.sml",
    "metamath": "AgentTarget.mm",
    "mizar": "AgentTarget.miz",
    "pvs": "AgentTarget.pvs",
}

STATEMENT_FENCE_ALIASES = {
    "lean4": {"lean", "lean4"},
    "rocq": {"coq", "rocq"},
    "isabelle": {"isabelle", "isabelle/hol"},
    "hol-light": {"hol-light", "hol_light", "hollight", "ocaml"},
    "acl2": {"acl2", "lisp"},
    "agda": {"agda"},
    "hol4": {"hol4", "sml", "standard-ml"},
    "metamath": {"metamath", "mm"},
    "mizar": {"mizar"},
    "pvs": {"pvs"},
}

PROVER_TIMEOUTS = {
    "lean4": 60,
    "rocq": 60,
    "isabelle": 120,
    "hol-light": 300,
    "acl2": 120,
    "agda": 120,
    "hol4": 300,
    "metamath": 60,
    "mizar": 300,
    "pvs": 300,
}

STATEMENT_TARGET_INSTRUCTIONS = {
    "lean4": (
        "Return a complete Lean file whose theorem proofs are left as `sorry`."
    ),
    "rocq": (
        "Return a complete Rocq file whose theorem proofs are left `Admitted`."
    ),
    "isabelle": (
        "Return a complete Isabelle theory whose theorem proofs are `sorry`."
    ),
    "hol-light": (
        "Bind each proposition as a quoted HOL term; do not call `prove`."
    ),
    "acl2": (
        "Encode the proposition as a predicate-valued `defun`, then emit "
        "`(value-triple :itpeval-statement-checked)` and `:q`; do not use "
        "proof or axiom-admission events."
    ),
    "agda": (
        "Encode the proposition as a type/Set definition; do not use "
        "`postulate` or provide an inhabitant."
    ),
    "hol4": (
        "Bind each proposition as a quoted HOL term. Do not call `prove`, "
        "`new_theory`, or `export_theory`; the verifier owns the theory wrapper."
    ),
    "metamath": (
        "Encode each unproved assertion with `$a`; do not use `$p`."
    ),
    "mizar": (
        "Return a complete article and wrap each unproved theorem between "
        "`::$P-` and `::$P+` with the required empty `proof end;` block."
    ),
    "pvs": (
        "Encode each proposition as a Boolean definition, not a LEMMA, "
        "THEOREM, AXIOM, or POSTULATE."
    ),
}

PROOF_TARGET_INSTRUCTIONS = {
    "lean4": "Return complete Lean declarations with checked proof terms.",
    "rocq": "Return complete Rocq declarations ending in checked `Qed` proofs.",
    "isabelle": "Return a complete Isabelle theory with checked proofs.",
    "hol-light": "Use `prove` (or an equivalent checked theorem constructor).",
    "acl2": (
        "Use checked `defthm` events; do not use `skip-proofs`, `defaxiom`, "
        "or constrained-event escape hatches."
    ),
    "agda": (
        "Return a complete module with inhabitants for the translated "
        "propositions; do not use `postulate` or holes."
    ),
    "hol4": (
        "Use checked HOL4 proof commands, but do not call `new_theory` or "
        "`export_theory`; the verifier owns the theory wrapper."
    ),
    "metamath": "Encode translated theorems as `$p` assertions with proofs.",
    "mizar": (
        "Return a complete checked article with real proof blocks; do not use "
        "parser proof-suppression pragmas."
    ),
    "pvs": (
        "Use LEMMA/THEOREM declarations with inline ProofLite `%|-` proof "
        "scripts so `proveit` can check the file."
    ),
}

EXTENDED_STMTS_MANIFEST = EVAL_DIR / "data" / "extended" / "manifest.json"

MODELS: list[dict] = [
    {"id": "gpt-5.5",                  "provider": "openai",      "label": "gpt-5.5"},
    {"id": "claude-sonnet-4-6",        "provider": "anthropic",   "label": "claude-sonnet-4-6"},
    {"id": "gemini-3.1-pro-preview",   "provider": "gemini",      "label": "gemini-3.1-pro-preview"},
    {"id": "deepseek/deepseek-v4-pro", "provider": "openrouter",  "label": "deepseek-v4-pro"},
    {"id": "qwen/qwen3-235b-a22b",     "provider": "openrouter",  "label": "qwen3-235b-a22b"},
]
