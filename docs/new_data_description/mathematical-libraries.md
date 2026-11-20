# Mathematical libraries

<span id="2-babel-formal"></span>

## Babel-formal

The extension uses Babel-formal’s Lean–Rocq developments. The paper’s cross-prover experiment covers **14 files and 117 aligned lemmas**. Its separate experiment translates 500 C-CoRN proofs from vanilla Rocq to SSReflect. [Paper, §2, pp. 2–3](https://github.com/LLM4Rocq/babel-formal/blob/main/paper/babel_formal.pdf) · [Source](https://github.com/LLM4Rocq/babel-formal)

The local index lists 16 topics and 143 lemmas. The ten-prover statement export includes **15 topics and 135 indexed lemmas**, counted as one record per topic and prover. [Topic index](../../data/babel-formal/data/index.json)

Topic descriptions summarize the local statements.

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

`supinf` has eight indexed lemmas, a nine-prover statement alignment and a place in the proof export. Topics such as `galois` and `integral_comp_neg_Iic` use axiomatized developments.

**Files:** `data/babel-formal/data/stmts/<prover>/<topic>.<ext>`.
Lean and Rocq are the primary source references for the extension.

<span id="7-logipedia"></span>

## Logipedia

Logipedia uses Dedukti to move mathematical developments between logical systems. The paper’s Matita arithmetic experiment covers about 300 lemmas, through Fermat’s little theorem. [Paper, “Empirical results”](https://arxiv.org/html/2305.00064v1)

The index has **469 declarations across 16 modules**. The extension includes **322 theorems and 72 axioms** in all ten provers. The other 75 entries provide context, such as definitions and type operators. [Index](../../data/logipedia/data/index.json)

### Exact module and declaration-type breakdown

Module names and declaration kinds come from the index. Descriptions summarize the inline statements.

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

The `nat` module accounts for 171 items. Keep the 72 axioms labelled as axioms in the statement dataset.

The index has inline Dedukti, Matita, Coq, Lean and PVS statements and OpenTheory availability metadata. The extension uses the indexed statements and module dependencies as its references.

**Files:** `data/logipedia/data/stmts/<prover>/<module>/<entry>.<ext>`.
The index uses dotted identities such as `fermat.congruent_exp_pred_SO`;
filesystem keys use `fermat/congruent_exp_pred_SO`.
