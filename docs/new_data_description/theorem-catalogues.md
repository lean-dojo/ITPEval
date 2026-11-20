# Named theorem catalogues

<span id="3-hundred-theorems"></span>

## Hundred Theorems

The statement export includes all **100** results from Freek Wiedijk’s catalogue, one item per catalogue number and one record per prover. [Formalizing 100 Theorems](https://www.cs.ru.nl/~freek/100/)

The local index retains titles, prover-specific identifiers and source links. Examples range from Cayley–Hamilton (49) and the central limit theorem (47) to incompleteness (6). [Local index](../../data/hundred-theorems/data/index.json)

Appendix A lists all 100 titles and marks the 58 entries in the proof export. [Catalogue membership](#appendix-a-exact-hundred-theorems-membership)

Some files keep library definitions and supporting declarations. Item 86 develops the lower Lebesgue integral. The formal target comes from the contract, source identifiers and reviewed resolutions. [Item 86](../../data/hundred-theorems/data/stmts/lean4/086_lebesgue_measure_and_integration.lean)

Files live at `data/hundred-theorems/data/stmts/<prover>/<NNN>_<slug>.<ext>`. Catalogue numbers and global evaluation `theorem_id` are separate identifiers.

<span id="8-thousand-theorems"></span>

## Thousand Theorems

The 1000+ Theorems project tracks named results from Wikipedia and links to their formalizations. ITPEval uses a selection of its catalogue IDs and recorded subject codes. [Catalogue](https://1000-plus.github.io/) · [Project description](https://1000-plus.github.io/about/)

The index lists **1,198** catalogue entries. The local extension selects **232** and has all ten representations for **227**. The index’s older `_stats.formalized_in_any = 202` describes the catalogue import. [Imported index](../../data/thousand-theorems/data/index.json)

<span id="exact-mathematical-domain-breakdown_1"></span>

### Exact mathematical-domain breakdown

Each of the 227 items has a two-digit Mathematics Subject Classification (MSC) code recorded in the local index. The items span 30 categories.

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

The five excluded identities are `Q189136` (mean value theorem), `Q338886`
(divergence theorem), `Q5165492` (continuous mapping theorem), `Q5445112`
(Fernique), and `Q642620` (Krein–Milman).

Indexed declarations and pinned sources guide the extension. References include Mathlib, Rocq, Isabelle/HOL and AFP, HOL Light, Metamath’s `set.mm` and Mizar’s MML. The table covers the 227 retained items.

**Files:** `data/thousand-theorems/data/stmts/<prover>/<QID>_<slug>.<ext>`.
Retain suffixes such as `Q180345X` and `Q1067156X`: these identify separate catalogue
entries and must not be collapsed into the unsuffixed Wikidata ID.

## Appendix A. Exact Hundred Theorems membership

All 100 rows are in the statement export. “Yes” marks proof export membership. Titles come from the index.

<details markdown="1">
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
