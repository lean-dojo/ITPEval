# Proof coverage and inventory audit

Check which datasets include proofs, how statement alignment was reviewed, and how to reproduce the counts.

<span id="10-proof-data-availability"></span>

## Proof data availability

The proof export uses evaluation `theorem_id` 1–74, with one record per item in **Lean 4, Rocq, Isabelle/HOL and HOL Light**. Membership comes only from the export. [Proof records](../../eval/data/proofs.json)

| Source | Aligned proof items | Proof records | Overlap with ten-prover statement items |
|---|---:|---:|---:|
| Babel-formal | 16 | 64 | 15 |
| Hundred Theorems | 58 | 232 | 58 |
| **Total** | **74** | **296** | **73** |

The export includes all 16 Babel topics, including `supinf`, and the 58 catalogue entries marked in [Appendix A](theorem-catalogues.md#appendix-a-exact-hundred-theorems-membership). A Babel file counts once even if it contains several lemmas.

<span id="11-extension-and-validation-boundaries"></span>

## Extension and validation boundaries

### What the ten-prover extension changes

The extension imports formal representations, fills missing statements and records reviewed resolutions where sources disagree. [Extension specification](../../corpus-extension/statement_translation_prompt.md)

| Source | Authority for the extended statement |
|---|---|
| Babel-formal | Lean/Rocq topic development; other original prover files provide secondary context |
| Hundred Theorems | Indexed theorem identity, actual source statements and any reviewed specification |
| miniF2F | Available aligned representations, with aliases resolved and source conflicts reviewed |
| PutnamBench | Published problem text, primary Lean reference and reviewed canonical resolutions |
| nTP4VC | Pinned Why3 goal; documented corrected source authorities where applicable |
| Logipedia | Inline indexed propositions and module dependency context |
| Thousand Theorems | Indexed prover declarations and pinned source files, not just theorem titles |
| VERINA | Official Lean program, helpers, contract and correctness proposition |

The reviewed Why3 changes include arithmetic and string-model axioms and a missing distinct-index premise. [Semantic resolutions](../../corpus-extension/semantic_canonical_resolutions.json) · [Why3 corrections](../../data/ntp4vc/data/corrected_why3_sources/README.md)

Statement records can carry definitions, assumptions, imports and a proof placeholder. The inventory checks membership and metadata. Native checks assess typechecking or proof completion, and equivalence checks compare statements’ meaning. [Evaluation checks](../guides/formalization-and-translation.md)

### Length and complexity: measured scope matters

The table counts full Lean 4 source lines, including blanks and comments. Measure proof difficulty and model context length separately.

| Source | Included items | Full Lean file lines: minimum | Median | Maximum |
|---|---:|---:|---:|---:|
| Babel-formal | 15 | 25 | 69 | 212 |
| Hundred Theorems | 100 | 12 | 129 | 5,678 |
| miniF2F | 455 | 7 | 8 | 24 |
| PutnamBench | 657 | 8 | 15 | 38 |
| nTP4VC | 597 | 222 | 371 | 575 |
| Logipedia | 394 | 4 | 15 | 57 |
| Thousand Theorems | 227 | 15 | 24 | 247 |
| VERINA | 189 | 54 | 65 | 158 |

Long Hundred Theorems and nTP4VC files often carry library definitions or standalone verification environments. Other provers may import or express those definitions differently.

### Limits on coverage claims

- **The units differ.** Topic files, catalogue results, axioms, competition problems,
  and program VCs should not be treated as interchangeable independent observations.
- **The ten-way intersection is selective.** The 59 exclusions are concentrated in
  particular source problems, so the retained set need not preserve the upstream
  subject or difficulty distribution.
- **Catalogue and topic overlap remains.** Hundred/Thousand Theorems can share
  mathematical content; VERINA has related task formulations; nTP4VC can contain
  several obligations from one program; Logipedia has dependency-related lemmas.
- **Source splits remain meaningful.** Keep miniF2F validation/test membership.
  nTP4VC's [upstream rules](https://github.com/xqyww123/NTP4VC#protection-to-prevent-data-leakage)
  protect all VCs from a selected Why3 source file/original C function against
  training leakage. Randomly splitting individual obligations would not reproduce
  that protocol.
- **Original task and translation task differ.** A benchmark's proof-synthesis or
  code-generation results do not directly measure cross-prover translation difficulty.
  No original-paper model success rate is presented as a result of this extension.

<span id="12-reproducing-the-local-counts"></span>

## Reproducing the local counts

Run the accompanying standard-library-only [audit script](../audit_extended_dataset.py)
from the repository root:

```bash
# Write the inventory audit as JSON for later comparison.
python3 docs/audit_extended_dataset.py > /tmp/extended-dataset-audit.json
```

The audit reports included and excluded IDs, missing representations, source metadata, Lean file sizes and proof membership. It verifies all eight statement totals and the **74 proof items, 296 records and 73 overlapping identities** using only Python’s standard library.

1. Match canonical dataset-scoped identities, not the minimum of ten directory sizes.
2. Restrict to the ten standard prover extensions; omit ACL2r and generated build files.
3. Use Lean candidate identities as the frame, except nTP4VC, which uses its pinned
   600-item selection. Resolve the seven miniF2F identity aliases in Appendix B.
4. Read the materialized nTP4VC statements, normalize leading `_` versus `X_`, and exclude unselected VCs.
5. Preserve miniF2F splits, Hundred catalogue numbers and Thousand catalogue suffixes.
6. Count proofs only from the `eval/data/proofs.json` export.

A statement record counts one `(item, prover)` slot. Additional alias files and
shared support modules do not create extra records, so 26,340 is not a raw count
of every file under the statement directories.

Local input metadata are the eight `data/<dataset>/data/index.json` files,
`data/ntp4vc/data/test_set.lean.txt.lst`, and
`data/putnambench/data/upstream_problem_metadata.json`. Upstream-paper-only distributions
(MATH levels; nTP4VC scenario/operation labels; VERINA code/specification sizes)
are deliberately not reconstructed from proxies.

### Primary references inspected

| Source | Inspected primary source and relevant location |
|---|---|
| Babel-formal | [Paper in author repository](https://github.com/LLM4Rocq/babel-formal/blob/main/paper/babel_formal.pdf), §2, pp. 2–3; [repository](https://github.com/LLM4Rocq/babel-formal) |
| Hundred Theorems | [Wiedijk's catalogue](https://www.cs.ru.nl/~freek/100/), introduction and numbered list |
| miniF2F | [Original paper](https://arxiv.org/html/2109.00110v1#S3), §3 and Table 1; [source repository](https://github.com/facebookresearch/miniF2F) |
| PutnamBench | [NeurIPS 2024 published paper](https://papers.neurips.cc/paper_files/paper/2024/file/1582eaf9e0cf349e1e5a6ee453100aa1-Paper-Datasets_and_Benchmarks_Track.pdf), §3, Tables 1–2, pp. 3–4; local copy of upstream problem metadata |
| nTP4VC | [Paper](https://arxiv.org/html/2601.18944v1#S4), §4, Tables 2–4, Appendix H; [pinned statistics](https://github.com/xqyww123/NTP4VC/tree/3ff8817c0fb04a5ef472a62a0fa5cd7a7934afe3/statistics) and [analysis script](https://github.com/xqyww123/NTP4VC/blob/3ff8817c0fb04a5ef472a62a0fa5cd7a7934afe3/tools/statistics_VC.py) |
| Logipedia | [Paper](https://arxiv.org/html/2305.00064v1), “Logical frameworks,” “Reverse mathematics,” and “Empirical results”; local indexed module statements |
| Thousand Theorems | [Catalogue](https://1000-plus.github.io/) and [project description](https://1000-plus.github.io/about/); local MSC-labelled index |
| VERINA | [Paper](https://arxiv.org/html/2505.23135v1#S3), §3.1–3.2 and Table 2; [source repository](https://github.com/sunblaze-ucb/verina) and local pinned task metadata |

The published PutnamBench paper reports **1,692 formalizations**. ArXiv v1 reports **1,697**, and the local import uses its own snapshot. These totals count formalizations of problems, which can each have several.

## Public export

The eight checksum-verified statement shards live in `eval/data/extended/`. The identity manifest is `eval/subsets/extended_stmts_2634.json`. Run `python3 data/build_eval_jsons.py --check` to compare them with the source bytes. The archived reference statements and proof records have separate exports.
