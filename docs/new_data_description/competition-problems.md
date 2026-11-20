# Competition problems

<span id="4-minif2f"></span>

## miniF2F

miniF2F contains **488** competition and textbook problems in validation and test splits of 244 each. The authors balanced each split by source and balanced MATH problems by difficulty. [Paper, §3 and Table 1](https://arxiv.org/html/2109.00110v1#S3)

### Exact source breakdown

The original column applies to each split. Local counts use canonical names. The IMO row includes shortlist entries such as `imosl_2007_algebra_p6`.

| Problem source/type | Original per split | Local test | Local valid | Local total |
|---|---:|---:|---:|---:|
| IMO / IMO-shortlist family | 20 | 14 | 16 | **30** |
| AIME | 15 | 15 | 15 | **30** |
| AMC, including AMC12/A/B | 45 | 41 | 40 | **81** |
| MATH: algebra | 70 | 65 | 66 | **131** |
| MATH: number theory | 60 | 59 | 59 | **118** |
| Custom: algebra | 18 | 18 | 16 | **34** |
| Custom: number theory | 8 | 8 | 8 | **16** |
| Custom: induction | 8 | 7 | 8 | **15** |
| **Total** | **244** | **227** | **228** | **455** |

The next table uses the paper’s original MATH difficulty counts. Exact retained counts require joining the original MATH records because the local index lacks item-level difficulty labels.

| MATH difficulty | Algebra, per original split | Number theory, per original split |
|---|---:|---:|
| Level 1 | 14 | 11 |
| Level 2 | 14 | 11 |
| Level 3 | 14 | 11 |
| Level 4 | 14 | 11 |
| Level 5 | 14 | 16 |
| **Total per split** | **70** | **60** |

The names `mathd_algebra_*` and `mathd_numbertheory_*` identify MATH problems. Prefixes such as `algebra_*`, `numbertheory_*` and `induction_*` identify custom exercises. [AIME 1983 P1](../../data/minif2f/data/stmts/lean4/test/aime_1983_p1.lean) · [Sum of cubes](../../data/minif2f/data/stmts/lean4/test/induction_sumkexp3eqsumksq.lean)

The source index records the miniF2F import, Lean 4 and Rocq ports, and partial HOL Light coverage. The extension fills statement slots. [Source index](../../data/minif2f/data/index.json) · [Upstream miniF2F](https://github.com/facebookresearch/miniF2F)

The seven aliases in Appendix B give 455 item identities across the ten provers. Literal filename matching yields 448. A file alias identifies a problem, with semantic equivalence evaluated separately.

Files live at `data/minif2f/data/stmts/<prover>/<test|valid>/<name>.<ext>`. Keep the split in the identity. The subset omits 17 test and 16 validation problems.

<span id="5-putnambench"></span>

## PutnamBench

PutnamBench formalizes problems from the undergraduate Putnam competition.
Some tasks ask you to find the answer and prove it. Others supply the answer and
ask for a proof. The published NeurIPS 2024 version contains **640 problems**
and **1,692 formalizations**, with 640 in Lean, 640 in Isabelle and 412 in Coq.
[Paper, §3, Tables 1–2 and “Factored Solutions”](https://papers.neurips.cc/paper_files/paper/2024/file/1582eaf9e0cf349e1e5a6ee453100aa1-Paper-Datasets_and_Benchmarks_Track.pdf)

The local pool has **674 identities**, with **657 ten-prover items** between 1962 and 2025. The local index’s 1,709 formalizations describe another snapshot.

### Exact mathematical-domain breakdown

The first numeric column is the paper's Table 2. The second joins our included IDs
to the imported [problem metadata](../../data/putnambench/data/upstream_problem_metadata.json).
These are **overlapping labels**, not disjoint bins.

| Upstream domain label | Paper: 640 problems | Local: 657 included problems |
|---|---:|---:|
| Algebra | 253 | **255** |
| Analysis | 226 | **218** |
| Number theory | 107 | **113** |
| Geometry | 68 | **68** |
| Linear algebra | 51 | **54** |
| Abstract algebra | 28 | **28** |
| Combinatorics | 26 | **35** |
| Probability | 9 | **14** |
| Set theory | 8 | **7** |
| **Total label assignments** | **776** | **792** |
| **Included items missing local tag metadata** | — | **2** |

Of the 655 labelled items, 527 have one tag, 119 have two and nine have three, for 792 labels total. The corpus retains `putnam_1987_a3` and `putnam_1996_a1` without subject labels.

### Contest position and time coverage

| Problem position | Session A | Session B | Combined |
|---|---:|---:|---:|
| 1 | 55 | 56 | 111 |
| 2 | 53 | 54 | 107 |
| 3 | 60 | 57 | 117 |
| 4 | 51 | 52 | 103 |
| 5 | 56 | 57 | 113 |
| 6 | 54 | 52 | 106 |
| **Total** | **329** | **328** | **657** |

The 1960s contributed 87 problems, the 1970s 95, the 1980s 97, the 1990s 99, the 2000s 103, the 2010s 111 and 2020–2025 another 65. The paper describes roughly increasing difficulty within a session. Use contest positions as positions, with difficulty measured separately.

**Import and extension.** Lean, Isabelle and Rocq are the original benchmark
languages. Published problem text and [canonical resolutions](../../corpus-extension/putnambench_canonical_resolutions.json)
govern local repairs where formal sources disagree. The audit lists all 17 excluded
IDs, including `putnam_2025_b6`.

**Files:** `data/putnambench/data/stmts/<prover>/putnam_<year>_<a|b><1–6>.<ext>`.

## Appendix B. miniF2F identity aliases used in the count

Canonical names follow the Lean 4 inventory. Alternate names record the matching items in other provers, including original contest-number typos.

| Canonical identity | Alternate identity or identities |
|---|---|
| `test/imosl_2007_algebra_p6` | `test/imo_2007_p6`; `test/imo_2007_a6` |
| `test/induction_sumkexp3eqsumksq` | `test/induction_sumkexp3eqsumksqsq` |
| `test/numbertheory_notEquiv2i2jasqbsqdiv8` | `test/numbertheory_notequiv2i2jasqbsqdiv8` |
| `valid/aimeII_2001_p3` | `valid/aimeI_2001_p3` |
| `valid/aime_1997_p11` | `valid/aime_1997_p12` |
| `valid/amc12a_2020_p21` | `valid/amc12a_2020_p22` |
| `valid/imo_2006_p3` | `valid/imo_2006_p6`; `valid/imo_2006_a6` |
