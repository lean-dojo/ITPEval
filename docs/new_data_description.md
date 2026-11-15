# ITPEval Dataset: Sources, Problem Types, and Exact Coverage

**Inventory audited:** 20 October 2026, at repository commit
`d346842e2b516040e04fe36ae03765e5fa2e5759`.
This retains the dataset scope previously recorded at `3c5b7a278`.
Upstream paper statistics and local inventory statistics are distinguished throughout.

The dataset combines **eight sources of mathematical statements and program-verification
problems**, represented in **Lean 4, Rocq, Isabelle/HOL, HOL Light, ACL2, Agda, HOL4,
Metamath, Mizar, and PVS**. The statement component has **2,634 aligned items /
26,340 prover records**. The available proof component has **74 items /
296 records in four provers**.

An **item** is a dataset-scoped identity: a problem, catalogue entry, verification
condition, or Babel topic file. A **record** is its representation in one prover
and one modality. A Babel item can contain several lemmas; a Logipedia item can be
an axiom. Consequently, **2,634 is not a count of independent proved theorems**.

## 1. Dataset overview

“Local pool” means the candidate identities considered for this extension before
requiring a statement representation in all ten systems. It does not mean every
file found recursively in a source checkout.

| Source | Original paper or catalogue scope | Local pool | Ten-prover items | Statement records | What an item contains |
|---|---|---:|---:|---:|---|
| [Babel-formal](#2-babel-formal) | Paper: 14 files, 117 lemmas, Lean–Rocq | 16 | **15** | 150 | An axiomatized mathematical theory with several lemmas |
| [Hundred Theorems](#3-hundred-theorems) | A catalogue of 100 named results | 100 | **100** | 1,000 | A catalogue theorem and its formal context |
| [miniF2F](#4-minif2f) | 488 problems: 244 test + 244 validation | 488 | **455** | 4,550 | A competition or textbook-style mathematics problem |
| [PutnamBench](#5-putnambench) | NeurIPS 2024: 640 problems, 1,692 formalizations | 674 | **657** | 6,570 | An undergraduate Putnam competition problem |
| [nTP4VC](#6-ntp4vc) | 600 selected verification conditions | 600 | **597** | 5,970 | One program-verification obligation and its environment |
| [Logipedia](#7-logipedia) | Arithmetic-library interoperability; local index: 469 declarations | 394 | **394** | 3,940 | One theorem or axiom; supporting declarations are excluded as items |
| [Thousand Theorems](#8-thousand-theorems) | A growing catalogue; local index: 1,198 entries | 232 | **227** | 2,270 | A selected named theorem identified by catalogue ID |
| [VERINA](#9-verina) | 189 Lean programming tasks | 189 | **189** | 1,890 | A program, precondition, postcondition, and correctness statement |
| **Total** | **8 sources** | **2,693** | **2,634** | **26,340** | |

The 59 omitted candidate items are 1 Babel, 33 miniF2F, 17 Putnam, 3 nTP4VC,
and 5 Thousand Theorems items. At this snapshot they lack an ordinary ACL2
statement; the other nine systems have representations. Supplemental **ACL2r is
not counted as ACL2** and is not shipped as a release adapter; nine-system items are outside the ten-system corpus.

The statement and proof components overlap on 73 dataset-scoped identities.
Their union is **2,635 items** and **26,636 modality-specific records**.
These are not deduplicated by mathematical content across benchmarks: the two
named-theorem catalogues, for example, can refer to the same mathematical result.

### How to read the breakdowns

- **Paper statistics** describe the authors’ release, with a paper/table locator.
- **Local counts using upstream labels** join included IDs to imported metadata.
- **Descriptive topic summaries** explain the files; they are not author-supplied difficulty labels.

File presence establishes inventory coverage. It does **not** independently certify
semantic equivalence, native checker acceptance, or completed proofs. See
[extension and validation boundaries](#11-extension-and-validation-boundaries).

## 2. Babel-formal

**Original benchmark.** Babel-formal studies proof translation between Lean and
Rocq, including translation through proof terms. Its cross-assistant benchmark
has **14 files / 117 aligned lemmas**. A separate vanilla-Rocq-to-SSReflect experiment
uses **500 C-CoRN proofs**; that experiment is not part of this extended dataset.
See the [paper, §2, pp. 2–3](https://github.com/LLM4Rocq/babel-formal/blob/main/paper/babel_formal.pdf)
and [author-maintained repository](https://github.com/LLM4Rocq/babel-formal).

**Local representation.** The [topic index](../data/babel-formal/data/index.json)
contains 16 topic files and 143 indexed lemma entries. The ten-prover intersection
retains **15 topics / 135 indexed lemma entries**. These count the index's `items`,
not every declaration or helper in each current source file. Each topic contributes
ten records regardless of its number of lemmas.

The topic descriptions below are based on the local statements. The paper does
not publish this 15-topic distribution.

| Exact topic ID | Indexed lemmas | Mathematical content and representation |
|---|---:|---|
| `circle_average` | 17 | Abstract averaging/integration: additivity, constants, argument shifts, invariance |
| `comp_commute` | 7 | Commuting functions, composition, identity, congruence and transport |
| `galois` | 14 | Field cancellation/inverses; axiomatized polynomial maps, splitting fields, solvability and towers |
| `graph_paths` | 8 | Inductively represented graph paths, transitivity, concatenation |
| `group` | 17 | Abstract group operations, cancellation, inverses, products |
| `ideals` | 2 | Closure properties of intersections and sums of ideals |
| `inner_product` | 6 | Inner-product identities for negation, addition, subtraction |
| `integral_comp_neg_Iic` | 16 | Ordered-field/set preliminaries; axiomatized integrals and substitution under negation |
| `lattice_like` | 6 | Meet/join identities in lattice-like structures |
| `limits_uniqueness` | 2 | An absolute-value inequality and uniqueness of limits |
| `linear_map` | 4 | Kernel/image closure under addition and scalar multiplication |
| `polynomial` | 12 | Roots, factors, evaluation and degree bounds; custom inductive naturals/lists in the context |
| `probability` | 11 | Event/set operations and identities for an axiomatized probability function |
| `set_algebra` | 4 | Distributivity and De Morgan identities |
| `zero_le_one_elem` | 9 | Entrywise matrix order/equality and comparison of zero and identity matrices |
| **Total** | **135** | **15 topic-file items** |

`supinf` has eight indexed lemmas and remains in the proof
corpus, but its statements are only nine-way aligned. Names such as `galois` and
`integral_comp_neg_Iic` describe **axiomatized developments** here; they should not
be read as complete constructions of Galois theory or measure theory from foundations.

**Files:** `data/babel-formal/data/stmts/<prover>/<topic>.<ext>`.
Lean and Rocq are the primary source references for the extension.

## 3. Hundred Theorems

**Original source.** Freek Wiedijk's [Formalizing 100 Theorems catalogue](https://www.cs.ru.nl/~freek/100/)
tracks formalizations of a numbered list of named mathematical results. It is a
catalogue rather than a paper-defined train/test benchmark. It supplies neither a
mutually exclusive subject taxonomy nor numerical difficulty levels. Upstream
formalization coverage varies by prover; it does not imply native proofs of all
100 results in every one of our ten systems.

**Local coverage is exactly catalogue IDs 1–100.** The
[local index](../data/hundred-theorems/data/index.json) preserves titles,
prover-specific identifiers and available source URLs. The contents range from the
triangle inequality (91), Cayley–Hamilton (49), and the fundamental theorem of
calculus (15), to Ramsey (31), the central limit theorem (47), incompleteness (6),
and continuum-hypothesis independence (24). These illustrate breadth, **not an
official category partition**.

The exact 100 titles and the 58 entries in the proof export are listed in
[Appendix A](#appendix-a-exact-hundred-theorems-membership). The other 42 entries
are included as ten-prover statements without being added to that proof corpus.

**What the files are.** Some are isolated statements; others retain substantial
library definitions and auxiliary declarations. For example,
[item 86](../data/hundred-theorems/data/stmts/lean4/086_lebesgue_measure_and_integration.lean)
contains a development of the lower Lebesgue integral. The formal contract,
source identifiers and reviewed resolutions determine the translation target;
a broad catalogue title alone does not specify the precise statement.

**Files:** `data/hundred-theorems/data/stmts/<prover>/<NNN>_<slug>.<ext>`.
Catalogue ID 17 is distinct from global evaluation `theorem_id` 17.

## 4. miniF2F

**Original benchmark.** The 488 problems form equally sized validation and test
splits, stratified by source and, for MATH-derived problems, difficulty. The
selection emphasizes algebra, number theory and inequalities; it does not cover
olympiad geometry and combinatorics comprehensively.
[Paper, §3 and Table 1](https://arxiv.org/html/2109.00110v1#S3).

### Exact source breakdown

“Original per split” applies separately to each 244-problem split. Local counts
use the same source families, identified by canonical names. The IMO family
includes shortlist identifiers such as `imosl_2007_algebra_p6`.

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

The paper's finer MATH breakdown is below. These are **original benchmark counts**,
not a measured difficulty distribution for the retained 455.

| MATH difficulty | Algebra, per original split | Number theory, per original split |
|---|---:|---:|
| Level 1 | 14 | 11 |
| Level 2 | 14 | 11 |
| Level 3 | 14 | 11 |
| Level 4 | 14 | 11 |
| Level 5 | 14 | 16 |
| **Total per split** | **70** | **60** |

The local index does not attach MATH difficulty levels to individual problems.
Exact post-filter level counts require joining the original MATH records;
filenames alone do not establish difficulty, so local level counts are not inferred.

**What the problems look like.** `mathd_algebra_*` and `mathd_numbertheory_*`
identify MATH exercises; competition prefixes encode year/problem identities;
`algebra_*`, `numbertheory_*` and `induction_*` identify custom exercises.
Examples include [AIME 1983 P1](../data/minif2f/data/stmts/lean4/test/aime_1983_p1.lean)
and [the sum-of-cubes identity](../data/minif2f/data/stmts/lean4/test/induction_sumkexp3eqsumksq.lean).

**Import and extension.** The [source index](../data/minif2f/data/index.json)
records imports from [facebookresearch/miniF2F](https://github.com/facebookresearch/miniF2F),
plus Lean 4 and Rocq ports. Existing HOL Light coverage was partial. The extension
fills missing representations and adds target systems; optional upstream proofs
are not thereby converted into a ten-prover proof corpus.

**Identity normalization.** Seven problem identities have differing names across
upstream representations. The mappings in Appendix B give 455 ten-prover identities;
literal filename matching gives 448. Additional HOL Light aliases are not extra
problems. This aligns identities, not a proof of equivalence between file contents.

**Files:** `data/minif2f/data/stmts/<prover>/<test|valid>/<name>.<ext>`.
The split remains part of the identity. Exclusions remove 17 test and 16 validation
problems; report this as an extended subset, not the full standard miniF2F test set.

## 5. PutnamBench

**Original benchmark.** The published NeurIPS 2024 version has **640 problems**:
**640 Lean, 640 Isabelle and 412 Coq formalizations**, totaling **1,692**.
It distinguishes finding a solution and proving it from proving a supplied solution;
answer definitions can be factored out of theorem statements.
[Published paper, §3, Tables 1–2 and “Factored Solutions,” pp. 3–4](https://papers.neurips.cc/paper_files/paper/2024/file/1582eaf9e0cf349e1e5a6ee453100aa1-Paper-Datasets_and_Benchmarks_Track.pdf).

**Local scope.** The pool contains **674 identities**, of which **657** have ten-prover
statements. Included years range from **1962 to 2025**. This differs from the paper's
640 and is not every problem from every year. The local index's prose about 1,709
formalizations is not the item count used here.

### Exact mathematical-domain breakdown

The first numeric column is the paper's Table 2. The second joins our included IDs
to the imported [problem metadata](../data/putnambench/data/upstream_problem_metadata.json).
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

Of the **655 locally labelled items**, 527 have one tag, 119 have two, and nine have
three. The two unlabelled included IDs are **`putnam_1987_a3` and `putnam_1996_a1`**.
They remain in the corpus; no subjects are guessed for them. Thus 792 counts label
assignments, while 657 counts problems.

The labels distinguish polynomial/inequality exercises, calculus and limits,
matrices, groups/rings, finite counting, and other mathematical domains. For the
exact problem and answer convention, inspect its formal file and informal metadata.

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

Decade counts: **1960s: 87; 1970s: 95; 1980s: 97; 1990s: 99; 2000s: 103;
2010s: 111; 2020–2025: 65**. The paper describes roughly increasing difficulty
within each session; contest position is not a measured model-difficulty label.

**Import and extension.** Lean, Isabelle and Rocq are the original benchmark
languages. Published problem text and [canonical resolutions](../corpus-extension/putnambench_canonical_resolutions.json)
govern local repairs where formal sources disagree. The audit lists all 17 excluded
IDs, including `putnam_2025_b6`.

**Files:** `data/putnambench/data/stmts/<prover>/putnam_<year>_<a|b><1–6>.<ext>`.

## 6. nTP4VC

**Original benchmark.** nTP4VC extracts proof obligations through Why3 and Frama-C,
then exports them to Lean, Rocq and Isabelle. Its **600 selected VCs** are split
between **300 program pearls** and **300 real-C verification conditions**. The
selection favors difficult obligations; it is not a random sample of all VCs.
[Paper, §4, Tables 2–4](https://arxiv.org/html/2601.18944v1#S4).

A VC is a proposition whose proof establishes a particular program property under
specified assumptions. One program can generate many VCs. Thus 597 local items
means **597 proof obligations**, not 597 different programs.

### Paper's verification-scenario taxonomy

The following counts are for the **original 600**, not the retained 597.

| Source family | Paper category | Original VCs | Property or problem type |
|---|---|---:|---|
| Program pearls | Algorithm | 55 | Algorithmic correctness |
| Program pearls | Data structure | 73 | Data-structure operations and invariants |
| Program pearls | Calculation | 66 | Computational/mathematical routines |
| Program pearls | Engineering | 54 | Verification-oriented programming tasks |
| Program pearls | Competition | 52 | Verification challenge problems |
| Real C | Function | 81 | Function contracts |
| Real C | Loop | 81 | Loop properties |
| Real C | Memory | 74 | Memory safety/properties |
| Real C | Invalid argument | 64 | Validity of operation arguments |
| **Total** | | **600** | |

The local index and selection manifest do not supply an item-to-category mapping
for all nine paper categories. We therefore do not claim exact retained counts
for those categories. The exact local breakdown that can be reproduced directly
is the source-project distribution below.

### Exact local source-project breakdown

These counts come from the [pinned 600-item manifest](../data/ntp4vc/data/test_set.lean.txt.lst)
and current file intersection. Project names correspond to Table 3 of the paper;
`klibc_stdio` and `klibc_string` are combined in its kLIBC row.

| Source project / local path group | Imported VCs | Ten-prover VCs | What it contributes |
|---|---:|---:|---|
| Why3 program pearls: `pearl/` | 300 | **299** | Algorithms, data structures, calculations, engineering, verification contests |
| Contiki linked lists: `frama_c/contiki_list` | 78 | **78** | Linked-list properties and memory relationships |
| Contiki allocator: `frama_c/contiki_memb` | 21 | **21** | Allocation and memory-block properties |
| C++ STL-derived algorithms: `frama_c/standard_algorithms` | 53 | **53** | Sorting, searching, heaps and sequence algorithms |
| X.509 parser: `frama_c/x509_parser` | 9 | **9** | Parser correctness and safety obligations |
| Linux scheduler: `frama_c/should_we_balance` | 24 | **24** | Scheduler balancing routine |
| Linux library functions: `frama_c/verker` | 85 | **85** | Verified kernel library routines |
| kLIBC stdio: `frama_c/klibc_stdio` | 3 | **3** | Standard-I/O routines |
| kLIBC strings: `frama_c/klibc_string` | 11 | **11** | String-library routines |
| Paparazzi/UAV mathematics: `frama_c/airborne` | 16 | **14** | Numerical routines involving rotations/quaternions |
| **Total** | **600** | **597** | **299 pearls + 298 real-C VCs** |

There are **no `examples/` items** in this selected 600, despite that category
being mentioned in the general local index. The broader source checkout contains
many more VCs; it is not the benchmark selection.

The three excluded canonical identities are:

- `frama_c/airborne/float_quat_of_rmat/float_quat_of_rmat_Why3_ide_VCfloat_quat_of_rmat_a00_max_post_goal9`
- `frama_c/airborne/float_quat_of_rmat/float_quat_of_rmat_Why3_ide_VCfloat_quat_of_rmat_a11_max_post_goal10`
- `pearl/register_allocation_DWP_wrapqtvc`

### Operation types and structural complexity

The upstream [operation-statistics artifact](https://github.com/xqyww123/NTP4VC/blob/3ff8817c0fb04a5ef472a62a0fa5cd7a7934afe3/statistics/statistics_VC.csv)
reports the following **overlapping** operation families, also presented in the
paper's Table 4. An individual VC can appear in several rows.

| Operation family | Original 600 VCs containing it |
|---|---:|
| Integer arithmetic | 578 |
| Nonlinear arithmetic | 118 |
| Floating-point-related arithmetic | 18 |
| Lists / sequences | 202 |
| Sets / maps / bags | 59 |
| Trees / strings / matrices | 26 |
| Memory operations | 297 |
| Custom datatypes | 247 |

The original all-VC row reports mean expression size about **583 atomic terms**,
mean depth **54.5**, and mean **10.8 quantifiers**. These are Isabelle-expression
statistics for the upstream 600, not token counts for the ten-prover extension.
The paper's Appendix H clarifies that its floating-point quantities are modeled
as reals without rounding error; this label does not imply IEEE floating-point verification.

The published CSV contains aggregate operation counts, while its companion
per-item CSV contains size/depth/dependency information without those operation
labels. Recomputing exact operation-family counts for the retained 597 would
require the underlying per-item classification or rerunning the authors' analysis.

**Concrete local examples.** The pearl portion includes
`pearl/binomial_heap_BinomialHeap_mergeqtvc`,
`pearl/imp/imp_SymbolicInterpreter_symbolic_interp_whileqtvc`, and
`pearl/verifythis_2024_challenge1_Top_smart_array_copy_0qtvc`.
These preserve program-specific definitions and assumptions, not just arithmetic
conclusions detached from their verification environment.

**Provenance and files.** The [source index](../data/ntp4vc/data/index.json) pins
upstream revision `3ff8817c0fb04a5ef472a62a0fa5cd7a7934afe3`.
The canonical key is the selected path with the `_vcg/<language>/` layer removed.
For Rocq/Isabelle, a leading `X_` sometimes corresponds to Lean's leading `_`.
The [upstream README](https://github.com/xqyww123/NTP4VC#the-benchmark)
explains the VC-to-Why3-source mapping. Original `.mlw` files, plus explicitly
reviewed corrections, govern the extension; exports are secondary references.

The public release materializes the three original prover representations as
ordinary statement files. Counts remain restricted to the **600 selected
identities** in the pinned manifest.

## 7. Logipedia

**Original source.** Logipedia is an interoperability project, not a competition
benchmark. The [paper's “Empirical results” section](https://arxiv.org/html/2305.00064v1)
describes translating Matita's arithmetic library, through Fermat's little theorem
(about 300 lemmas), via Dedukti to other proof assistants. The project expresses
logical systems in a common framework and identifies fragments that can be shared.
That approximate paper count is different from our exact declaration inventory.

**Local selection.** The [index](../data/logipedia/data/index.json) contains
**469 declarations in 16 modules**: **322 theorems, 72 axioms, and 75 other
entries**. The extension includes the **394 theorem/axiom entries**; definitions,
constants and type operators are supporting context, not additional benchmark items.
All 394 have ten-prover representations.

### Exact module and declaration-type breakdown

The counts use the index's `module` and `kind` fields. Content descriptions summarize
its inline formal statements; the module names and declaration kinds are upstream metadata.

| Module | Theorems | Axioms | Included items | Content |
|---|---:|---:|---:|---|
| `connectives` | 0 | 13 | 13 | Primitive logical connectives and their laws |
| `leibniz` | 1 | 1 | 2 | Leibniz equality |
| `logic` | 14 | 2 | 16 | Logical introduction/elimination and equality rules |
| `relations` | 1 | 0 | 1 | Relations and reflexive closure |
| `bool` | 9 | 3 | 12 | Booleans, cases and Boolean operations |
| `nat` | 146 | 25 | 171 | Natural-number arithmetic, induction, order and comparisons |
| `div_mod` | 25 | 8 | 33 | Division and remainder |
| `bigops` | 25 | 6 | 31 | Finite aggregate operations and reindexing |
| `primes` | 17 | 2 | 19 | Primality and divisibility |
| `cong` | 11 | 0 | 11 | Modular congruence |
| `exp` | 7 | 3 | 10 | Exponentiation |
| `fact` | 6 | 3 | 9 | Factorial |
| `gcd` | 29 | 3 | 32 | Greatest common divisors and coprimality |
| `permutation` | 24 | 3 | 27 | Finite permutations and inverses |
| `sigma_pi` | 2 | 0 | 2 | Identities for finite products and powers |
| `fermat` | 5 | 0 | 5 | Fermat-related modular arithmetic |
| **Total** | **322** | **72** | **394** | |

This is concentrated coverage of logic and natural-number arithmetic, rather than
394 unrelated mathematical domains. The `nat` module alone contributes 171 items.
The 72 axioms are legitimate statement-translation inputs, but should remain
labelled as axioms; they are not 72 supplied theorem proofs.

**Import and extension.** The index supplies inline statements in Dedukti, Matita,
Coq, Lean and PVS, with OpenTheory availability metadata. These are source export
systems, not the ten systems of our extension. Module context and dependencies
matter: a theorem name such as `nat.plus` is not a standalone definition of addition.
The primary references are the indexed statements and their original module context.

**Files:** `data/logipedia/data/stmts/<prover>/<module>/<entry>.<ext>`.
The index uses dotted identities such as `fermat.congruent_exp_pred_SO`;
filesystem keys use `fermat/congruent_exp_pred_SO`.

## 8. Thousand Theorems

**Original source.** The [1000+ Theorems catalogue](https://1000-plus.github.io/)
tracks named results and links to formalizations in several proof assistants.
Its [project description](https://1000-plus.github.io/about/) explains that entries
come from Wikipedia's list of theorems. It is a growing catalogue, not a benchmark
with exactly 1,000 problems, a fixed difficulty distribution, or an original
benchmark paper defining train/test splits.

**Local selection.** The [imported index](../data/thousand-theorems/data/index.json)
contains **1,198 catalogue entries**. There are **232 candidate item identities**
in the local extension, of which **227** have all ten representations. The index's
older `_stats.formalized_in_any = 202` is a catalogue-import statistic, not the
current extended-file inventory.

### Exact mathematical-domain breakdown

Each included entry has one recorded two-digit **Mathematics Subject Classification
(MSC)** field. The following partition uses those fields unchanged, with abbreviated
subject descriptions. It has **30 populated categories** and sums to **227**.
Example titles and IDs come from the local index.

| MSC | Recorded subject area | Included items | Example included identity |
|---|---|---:|---|
| 03 | Logic and foundations | 15 | `Q1033910` — Cantor–Bernstein–Schroeder |
| 05 | Combinatorics | 16 | `Q1032886` — Hales–Jewett |
| 06 | Order and lattices | 6 | `Q17005116` — Birkhoff representation |
| 11 | Number theory | 31 | `Q1186808` — Lucas |
| 12 | Fields and polynomials | 9 | `Q180345` — rational root theorem |
| 13 | Commutative algebra | 7 | `Q172298` — Lasker–Noether |
| 14 | Algebraic geometry | 2 | `Q1068976` — Hilbert Nullstellensatz |
| 15 | Linear/multilinear algebra | 7 | `Q303402` — rank–nullity |
| 16 | Associative rings and algebras | 6 | `Q1065966` — isomorphism theorem |
| 17 | Nonassociative rings and algebras | 1 | `Q20971632` — Lie's theorem |
| 18 | Category theory / homological algebra | 2 | `Q4878586` — Beck monadicity |
| 20 | Group theory | 10 | `Q1057919` — Sylow |
| 26 | Real functions | 22 | `Q1137206` — Taylor |
| 28 | Measure and integration | 15 | `Q1067156` — dominated convergence |
| 30 | Functions of a complex variable | 14 | `Q1008566` — Gauss–Lucas |
| 32 | Several complex variables | 1 | `Q3527219` — Weierstrass preparation |
| 33 | Special functions | 1 | `Q2734084` — Bohr–Mollerup |
| 34 | Ordinary differential equations | 1 | `Q530152` — Picard–Lindelöf |
| 35 | Partial differential equations | 1 | `Q9993851` — Lax–Milgram |
| 37 | Dynamical systems / ergodic theory | 1 | `Q226014` — Poincaré recurrence |
| 42 | Harmonic analysis on Euclidean spaces | 2 | `Q2096184` — Plancherel |
| 43 | Abstract harmonic analysis | 2 | `Q3984053` — Fourier inversion |
| 46 | Functional analysis | 13 | `Q1426292` — Banach–Steinhaus |
| 51 | Geometry | 14 | `Q11518` — Pythagorean theorem |
| 52 | Convex/discrete geometry | 4 | `Q1632433` — Helly |
| 54 | General topology | 8 | `Q1052678` — Baire category |
| 57 | Manifolds and cell complexes | 1 | `Q1306095` — Whitney embedding |
| 60 | Probability and stochastic processes | 9 | `Q190391` — central limit theorem |
| 68 | Computer science | 4 | `Q1893717` — Rice |
| 91 | Game theory and economics | 2 | `Q33481` — Arrow impossibility |
| **Total** | **30 categories** | **227** | |

These are the **catalogue's recorded codes**, not a new reassignment of theorems
by their possible mathematical applications. An entry can naturally relate to more
than one field even though this metadata records one code.

The five excluded identities are `Q189136` (mean value theorem), `Q338886`
(divergence theorem), `Q5165492` (continuous mapping theorem), `Q5445112`
(Fernique), and `Q642620` (Krein–Milman).

**Import and extension.** Source links span Mathlib, Rocq libraries, Isabelle/HOL
and AFP, HOL Light, Metamath/set.mm, and Mizar/MML. Available indexed declarations
and pinned source files provide the formal references; catalogue titles alone
are insufficient. The ten-prover extension is a selected subset of this catalogue,
so its subject distribution should not be attributed to all 1,198 entries.

**Files:** `data/thousand-theorems/data/stmts/<prover>/<QID>_<slug>.<ext>`.
Retain suffixes such as `Q180345X` and `Q1067156X`: these identify separate catalogue
entries and must not be collapsed into the unsuffixed Wikidata ID.

## 9. VERINA

**Original benchmark.** VERINA evaluates code, specification and proof generation,
separately and in combination, using **189 Lean programming tasks**. Each task
has a description, implementation, pre/postconditions and tests; reference proofs
are optional. The original paper reports proofs for **46 of 189** tasks.
[Paper, §3.1–3.2, Table 2](https://arxiv.org/html/2505.23135v1#S3).

### Exact origin and difficulty-group breakdown

The paper's construction counts agree with the [local task index](../data/verina/data/index.json).
All 189 tasks are retained in the ten-prover statement corpus.

| Paper subset | Upstream source | Exact local task IDs | Tasks | What these data are |
|---|---|---|---:|---|
| VERINA-basic | MBPP-DFY-50; local origin `dafny-synthesis` | `verina_basic_1`–`verina_basic_49` | **49** | Human-authored Dafny programming problems translated into Lean |
| VERINA-basic | CloverBench; local origin `clover` | `verina_basic_50`–`verina_basic_108` | **59** | Additional Dafny examples translated and reviewed |
| VERINA-adv | Course submissions; local origin `lab_assignment` | `verina_advanced_1`–`verina_advanced_81` | **81** | More advanced tasks formalized in Lean; sources include LeetCode/LiveCodeBench-style problems |
| **Total** | **3 origins** | **108 basic + 81 advanced** | **189** | |

The paper does not publish a numerical partition into sorting, strings, dynamic
programming, etc. The local metadata also does not consistently identify individual
LeetCode/LiveCodeBench origins within the 81 course submissions; those platform
counts cannot be recovered from the broad `lab_assignment` label.

For concrete contents, the local signatures identify `verina_basic_1`
(`hasOppositeSign`), `_18` (`sumOfDigits`), `_19` (`isSorted`),
`verina_advanced_2` and `_3` (`LongestCommonSubsequence`), and advanced `_16` and
`_17` (`insertionSort`). Different task IDs can describe related algorithms or
alternative formulations; 189 is not a deduplicated count of algorithm families.

### Paper's code/specification size measurements

These count the relevant program/specification portions, **not full local files**.

| Subset | Code lines: median / maximum | Specification lines: median / maximum |
|---|---:|---:|
| Basic | 6 / 26 | 2 / 17 |
| Advanced | 16 / 38 | 7 / 62 |
| All tasks | 9 / 38 | 4 / 62 |

**What is extended.** Our item is the **complete correctness package**: relevant
helpers, precondition, executable program, postcondition and correctness proposition.
Translation must preserve the program's computation as well as its contract.
This corpus is not a new execution of VERINA's original code-generation or
specification-generation protocol, and its 189 imported Lean files are not 189
completed reference proofs.

**Pinned import.** The source revision is
`66b3ce5014edafb20cb26b87c681e7f31847249f`. The [local import notes](../data/verina/README.md)
document proof-body removal and six compatibility-normalized statements:
constructor renames in basic 22 and advanced 28/55/74; omission of unused,
proof-only Float axioms in basic 25/63. The original Lean files are retained.

**Files:** `data/verina/data/stmts/<prover>/<task-id>.<ext>`;
[descriptions](../data/verina/data/descriptions) and
[metadata](../data/verina/data/metadata) retain the informal tasks and signatures.

## 10. Proof data availability

The available proof records are stored in
[`eval/data/proofs.json`](../eval/data/proofs.json), with evaluation `theorem_id`
1–74. Each item has one proof record in **Lean 4, Rocq, Isabelle/HOL, and HOL Light**.
Later files under raw `data/*/data/proofs/` directories do not enlarge this component.

| Source | Aligned proof items | Proof records | Overlap with ten-prover statement items |
|---|---:|---:|---:|
| Babel-formal | 16 | 64 | 15 |
| Hundred Theorems | 58 | 232 | 58 |
| **Total** | **74** | **296** | **73** |

All 16 Babel topics are included here, including `supinf`. Appendix A marks the
exact 58 Hundred Theorems catalogue identities. A multi-lemma Babel file is still
one proof item; the table does not count individual proof steps or lemmas.

## 11. Extension and validation boundaries

### What the ten-prover extension changes

The source benchmarks were not originally all ten-prover datasets. This repository
imports available formal representations, supplies missing statement representations,
and records semantic repairs where sources disagree. The
[extension specification](../corpus-extension/statement_translation_prompt.md)
defines the source authority for each benchmark. In particular:

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

The [semantic-resolution record](../corpus-extension/semantic_canonical_resolutions.json)
and [corrected Why3 source notes](../data/ntp4vc/data/corrected_why3_sources/README.md)
are part of this provenance. For example, the Why3 corrections document changes
to arithmetic/string-model axioms and a missing distinct-index premise. Such
changes mean the current extension should not be described as a byte-for-byte
copy of an upstream paper's release.

A statement record may contain definitions, assumptions, imports, support references,
and proof placeholders. These representations vary substantially between provers.
**A successful statement check is not a completed proof**, and file-presence
alignment is not an independent semantic-equivalence judgment. This documentation
audit did not rerun every native prover or repeat the semantic review; it reports
membership and metadata, rather than a new validated-success total.

### Length and complexity: measured scope matters

The following measurements are recomputed from the **current Lean 4 file for each
included item**, counting all physical lines, including comments and blank lines.
They describe packaging and input size. They are not token estimates, minimal
statement lengths, proof lengths, or standardized difficulty scores.

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

The largest Hundred Theorems files contain library development context; nTP4VC
files retain substantial standalone verification environments. Conversely, a short
Putnam statement can require a difficult proof. Source-file length, mathematical
domain, dependency burden, quantification and original benchmark difficulty are
separate dimensions. Measurements from one prover also do not establish the
length of its representation in another prover.

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

## 12. Reproducing the local counts

Run the accompanying standard-library-only [audit script](audit_extended_dataset.py)
from the repository root:

```bash
python3 docs/audit_extended_dataset.py > /tmp/extended-dataset-audit.json
```

The output contains **every included identity**, every excluded identity, missing
representations by prover, miniF2F source/split counts, Putnam tags and positions,
nTP4VC source-project counts, Logipedia declaration kinds, Thousand Theorems MSC
counts, VERINA origins, full Lean-file line counts, and proof-corpus membership.
It asserts the documented eight statement totals and the **74 proof items / 296
proof records / 73 overlapping identities**. It does not invoke any prover or model.

The counting rules are:

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

The source links and version-specific locations recorded by the dataset audit
are listed below.

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

The published PutnamBench paper is used for its **1,692** formalization count;
the early arXiv v1 reports **1,697**, and the local import describes yet another
snapshot. These version-specific counts must not be conflated with distinct problem counts.

## Appendix A. Exact Hundred Theorems membership

All 100 rows belong to the ten-prover statement component. “Proof” marks inclusion
in the **proof component**. Titles are from the local index;
this table supplies exact membership without inventing an upstream subject taxonomy.

<details>
<summary>Expand the 100 catalogue entries and their proof-component membership</summary>

| Catalogue ID | Indexed theorem title | Proof record available? |
|---:|---|:---:|
| 1 | The Irrationality of the Square Root of 2 | Yes |
| 2 | The Fundamental Theorem of Algebra | Yes |
| 3 | The Denumerability of the Rational Numbers | Yes |
| 4 | Pythagorean Theorem | Yes |
| 5 | The Prime Number Theorem | — |
| 6 | Gödel's Incompleteness Theorem | — |
| 7 | Law of Quadratic Reciprocity | Yes |
| 8 | The Impossibility of Trisecting the Angle and Doubling the Cube | — |
| 9 | The Area of a Circle | — |
| 10 | Euler's Generalization of Fermat's Little Theorem | Yes |
| 11 | The Infinitude of Primes | Yes |
| 12 | The Independence of the Parallel Postulate | — |
| 13 | Polyhedron Formula | — |
| 14 | Euler's Summation of 1 + (1/2)^2 + (1/3)^2 + ... | Yes |
| 15 | The Fundamental Theorem of Integral Calculus | Yes |
| 16 | Insolvability of General Higher Degree Equations (Abel-Ruffini) | — |
| 17 | De Moivre's Theorem | Yes |
| 18 | Liouville's Theorem and the Construction of Transcendental Numbers | Yes |
| 19 | Four Squares Theorem | Yes |
| 20 | All Primes (1 mod 4) Equal the Sum of Two Squares | — |
| 21 | Green's Theorem | — |
| 22 | The Non-Denumerability of the Continuum | Yes |
| 23 | Formula for Pythagorean Triples | — |
| 24 | The Undecidability of the Continuum Hypothesis | — |
| 25 | Schroeder-Bernstein Theorem | Yes |
| 26 | Leibniz's Series for Pi | Yes |
| 27 | Sum of the Angles of a Triangle | Yes |
| 28 | Pascal's Hexagon Theorem | — |
| 29 | Feuerbach's Theorem | — |
| 30 | The Ballot Problem | Yes |
| 31 | Ramsey's Theorem | — |
| 32 | The Four Color Problem | — |
| 33 | Fermat's Last Theorem | — |
| 34 | Divergence of the Harmonic Series | Yes |
| 35 | Taylor's Theorem | Yes |
| 36 | Brouwer Fixed Point Theorem | — |
| 37 | The Solution of a Cubic | Yes |
| 38 | Arithmetic Mean / Geometric Mean | Yes |
| 39 | Solutions to Pell's Equation | — |
| 40 | Minkowski's Fundamental Theorem | — |
| 41 | Puiseux's Theorem | — |
| 42 | Sum of the Reciprocals of the Triangular Numbers | Yes |
| 43 | The Isoperimetric Theorem | — |
| 44 | The Binomial Theorem | Yes |
| 45 | The Partition Theorem (Euler) | — |
| 46 | The Solution of the General Quartic Equation | Yes |
| 47 | The Central Limit Theorem | — |
| 48 | Dirichlet's Theorem | — |
| 49 | The Cayley-Hamilton Theorem | Yes |
| 50 | The Number of Platonic Solids | — |
| 51 | Wilson's Theorem | Yes |
| 52 | The Number of Subsets of a Set | Yes |
| 53 | Pi is Transcendental | — |
| 54 | Königsberg Bridges Problem | Yes |
| 55 | Product of Segments of Chords | Yes |
| 56 | The Hermite-Lindemann Transcendence Theorem | — |
| 57 | Heron's Formula | Yes |
| 58 | Formula for the Number of Combinations | Yes |
| 59 | The Laws of Large Numbers | — |
| 60 | Bézout's Theorem | Yes |
| 61 | Theorem of Ceva | Yes |
| 62 | Fair Games Theorem (Optional Stopping) | — |
| 63 | Cantor's Theorem | Yes |
| 64 | L'Hôpital's Rule | Yes |
| 65 | Isosceles Triangle Theorem | Yes |
| 66 | Sum of a Geometric Series | Yes |
| 67 | e is Transcendental | — |
| 68 | Sum of an Arithmetic Series | — |
| 69 | Greatest Common Divisor Algorithm | Yes |
| 70 | The Perfect Number Theorem | Yes |
| 71 | Order of a Subgroup (Lagrange's Theorem) | Yes |
| 72 | Sylow's Theorem | Yes |
| 73 | Ascending or Descending Sequences (Erdős–Szekeres) | Yes |
| 74 | The Principle of Mathematical Induction | — |
| 75 | The Mean Value Theorem | Yes |
| 76 | Fourier Series | — |
| 77 | Sum of kth Powers | Yes |
| 78 | The Cauchy-Schwarz Inequality | Yes |
| 79 | The Intermediate Value Theorem | Yes |
| 80 | The Fundamental Theorem of Arithmetic | — |
| 81 | Divergence of the Prime Reciprocal Series | — |
| 82 | Dissection of Cubes (into Cubes) | — |
| 83 | The Friendship Theorem | Yes |
| 84 | Morley's Theorem | — |
| 85 | Divisibility by 3 Rule | Yes |
| 86 | Lebesgue Measure and Integration | — |
| 87 | Desargues's Theorem | — |
| 88 | Derangements Formula | Yes |
| 89 | The Factor and Remainder Theorems | Yes |
| 90 | Stirling's Formula | Yes |
| 91 | The Triangle Inequality | Yes |
| 92 | Pick's Theorem | — |
| 93 | The Birthday Problem | Yes |
| 94 | The Law of Cosines | Yes |
| 95 | Ptolemy's Theorem | Yes |
| 96 | Principle of Inclusion / Exclusion | Yes |
| 97 | Cramer's Rule | Yes |
| 98 | Bertrand's Postulate | Yes |
| 99 | Buffon Needle Problem | — |
| 100 | Descartes Rule of Signs | — |

</details>

## Appendix B. miniF2F identity aliases used in the count

Canonical names use the local Lean 4 frame. Alternate names below occur in other
prover directories. Some alternate names retain upstream contest-number typos;
this table records correspondence of benchmark items, not corrected competition nomenclature.

| Canonical identity | Alternate identity or identities |
|---|---|
| `test/imosl_2007_algebra_p6` | `test/imo_2007_p6`; `test/imo_2007_a6` |
| `test/induction_sumkexp3eqsumksq` | `test/induction_sumkexp3eqsumksqsq` |
| `test/numbertheory_notEquiv2i2jasqbsqdiv8` | `test/numbertheory_notequiv2i2jasqbsqdiv8` |
| `valid/aimeII_2001_p3` | `valid/aimeI_2001_p3` |
| `valid/aime_1997_p11` | `valid/aime_1997_p12` |
| `valid/amc12a_2020_p21` | `valid/amc12a_2020_p22` |
| `valid/imo_2006_p3` | `valid/imo_2006_p6`; `valid/imo_2006_a6` |

## Public export

The public release exports these statements in eight checksum-verified shards under
`eval/data/extended/`. Its exact path/identity manifest is
`eval/subsets/extended_stmts_2634.json`. Run `python3 data/build_eval_jsons.py --check`
to compare the exports against their source bytes without writing. The archived `eval/data/stmts.json` reference export and
`proofs.json` proof records are retained separately from the statement shards.
