# Released datasets

The ten-prover statement export contains **2,634 items from eight sources** and **26,340 records**. The four-prover proof export covers **74 items and 296 records**. [Load the records](benchmarks/translation.md#data-access-and-validation)

An item is a source unit, such as a miniF2F problem or a Babel-formal topic. A record is that item’s representation in one prover. The audit uses the data pinned in `eval/benchmark-lock.json`. [Reproduce the inventory](new_data_description/coverage-and-audit.md#12-reproducing-the-local-counts)

## Chapters

- <span id="3-hundred-theorems"></span><span id="8-thousand-theorems"></span><span id="exact-mathematical-domain-breakdown_1"></span><span id="appendix-a-exact-hundred-theorems-membership"></span>[Named theorem catalogues](new_data_description/theorem-catalogues.md)
  Find which Hundred Theorems and Thousand Theorems entries are in the statement and proof exports.
- <span id="4-minif2f"></span><span id="exact-source-breakdown"></span><span id="5-putnambench"></span><span id="exact-mathematical-domain-breakdown"></span><span id="contest-position-and-time-coverage"></span><span id="appendix-b-minif2f-identity-aliases-used-in-the-count"></span>[Competition problems](new_data_description/competition-problems.md)
  Compare miniF2F and PutnamBench coverage by source split, subject and competition.
- <span id="2-babel-formal"></span><span id="7-logipedia"></span><span id="exact-module-and-declaration-type-breakdown"></span>[Mathematical libraries](new_data_description/mathematical-libraries.md)
  See which Babel-formal topics and Logipedia declarations are included.
- <span id="6-ntp4vc"></span><span id="papers-verification-scenario-taxonomy"></span><span id="exact-local-source-project-breakdown"></span><span id="operation-types-and-structural-complexity"></span><span id="9-verina"></span><span id="exact-origin-and-difficulty-group-breakdown"></span><span id="papers-codespecification-size-measurements"></span>[Program verification](new_data_description/program-verification.md)
  Inspect the nTP4VC verification conditions and VERINA programming tasks.
- <span id="10-proof-data-availability"></span><span id="11-extension-and-validation-boundaries"></span><span id="what-the-ten-prover-extension-changes"></span><span id="length-and-complexity-measured-scope-matters"></span><span id="limits-on-coverage-claims"></span><span id="12-reproducing-the-local-counts"></span><span id="primary-references-inspected"></span><span id="public-export"></span>[Proof coverage and inventory audit](new_data_description/coverage-and-audit.md)
  Check which datasets include proofs, how statement alignment was reviewed, and how to reproduce the counts.

<span id="1-dataset-overview"></span>

## Source coverage

The local pool counts candidate items before the ten-prover requirement. Support files and alternate representations can share an item’s directory.

| Source | Original paper or catalogue scope | Local pool | Ten-prover items | Statement records | What an item contains |
|---|---|---:|---:|---:|---|
| [Babel-formal](new_data_description/mathematical-libraries.md#2-babel-formal) | Paper: 14 files, 117 lemmas, Lean–Rocq | 16 | **15** | 150 | An axiomatized mathematical theory with several lemmas |
| [Hundred Theorems](new_data_description/theorem-catalogues.md#3-hundred-theorems) | A catalogue of 100 named results | 100 | **100** | 1,000 | A catalogue theorem and its formal context |
| [miniF2F](new_data_description/competition-problems.md#4-minif2f) | 488 problems: 244 test + 244 validation | 488 | **455** | 4,550 | A competition or textbook-style mathematics problem |
| [PutnamBench](new_data_description/competition-problems.md#5-putnambench) | NeurIPS 2024: 640 problems, 1,692 formalizations | 674 | **657** | 6,570 | An undergraduate Putnam competition problem |
| [nTP4VC](new_data_description/program-verification.md#6-ntp4vc) | 600 selected verification conditions | 600 | **597** | 5,970 | One program-verification obligation and its environment |
| [Logipedia](new_data_description/mathematical-libraries.md#7-logipedia) | Arithmetic-library interoperability; local index: 469 declarations | 394 | **394** | 3,940 | One theorem or axiom; supporting declarations are excluded as items |
| [Thousand Theorems](new_data_description/theorem-catalogues.md#8-thousand-theorems) | A growing catalogue; local index: 1,198 entries | 232 | **227** | 2,270 | A selected named theorem identified by catalogue ID |
| [VERINA](new_data_description/program-verification.md#9-verina) | 189 Lean programming tasks | 189 | **189** | 1,890 | A program, precondition, postcondition, and correctness statement |
| **Total** | **8 sources** | **2,693** | **2,634** | **26,340** | |

All 59 omissions lack an ordinary ACL2 statement at this snapshot. The other nine systems have representations. The omissions are 1 Babel, 33 miniF2F, 17 Putnam, 3 nTP4VC and 5 Thousand Theorems items. Supplemental ACL2r stays outside both the ten-prover count and the shipped adapters.

The exports overlap on 73 dataset-scoped items. Their union contains **2,635 items** and **26,636 modality-specific records**. The same mathematical result may appear in more than one source.

### How to read the breakdowns

- **Paper statistics** describe the authors’ release. Follow the linked paper or table for the original counting method.
- **Local counts using upstream labels** match the included IDs to the labels in the imported metadata.
- **Descriptive topic summaries** explain the files in this repository. Use the author’s labels for experiments that need published difficulty ratings.

Use separate evidence for native acceptance, proof completion or statement equivalence. [Validation boundaries](new_data_description/coverage-and-audit.md#11-extension-and-validation-boundaries)
