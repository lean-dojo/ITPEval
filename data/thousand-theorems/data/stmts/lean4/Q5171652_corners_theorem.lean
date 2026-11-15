-- Statement-only formalization of Thousand Theorems artifact Q5171652
-- (thousand-theorems__lean4__Q5171652), "Corners theorem": every sufficiently
-- dense finite subset of an initial square of natural numbers contains a
-- nontrivial corner once the side length meets the explicit bound. This file contains no proof.

module

import Mathlib.Analysis.Normed.Group.AddCircle
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Data.Finset.Range

open Finset Function Real

namespace Q5171652

variable {n : ℕ} {ε : ℝ}

/-- The partition-size growth step in the explicit Szemerédi regularity bound. -/
def stepBound (n : ℕ) : ℕ :=
  n * 4 ^ n

/--
The real logarithm, represented as the unique inverse-exponential value on the
absolute value of a nonzero input and as zero at zero.
-/
noncomputable def realLog (x : ℝ) : ℝ :=
  letI := Classical.propDecidable
  if x = 0 then 0
  else if h : ∃ y : ℝ, Real.exp y = |x| then Classical.choose h else 0

/-- The initial partition size in the explicit Szemerédi regularity bound. -/
noncomputable def initialBound (ε : ℝ) (l : ℕ) : ℕ :=
  max 7 <| max l <| ⌊realLog (100 / ε ^ 5) / realLog 4⌋₊ + 1

/-- The explicit partition-size bound used by the triangle removal lemma. -/
noncomputable def regularityBound (ε : ℝ) (l : ℕ) : ℕ :=
  (stepBound^[⌊4 / ε ^ 5⌋₊] <| initialBound ε l) *
    16 ^ (stepBound^[⌊4 / ε ^ 5⌋₊] <| initialBound ε l)

/-- The explicit density constant in the triangle removal lemma. -/
noncomputable def triangleRemovalBound (ε : ℝ) : ℝ :=
  min (2 * ⌈4 / ε⌉₊ ^ 3)⁻¹
    ((1 - min 1 ε / 4) * (ε / (16 * regularityBound (ε / 8) ⌈4 / ε⌉₊)) ^ 3)

/-- The explicit density threshold used in the corners theorem. -/
noncomputable def cornersTheoremBound (ε : ℝ) : ℕ :=
  ⌊(triangleRemovalBound (ε / 9) * 27)⁻¹⌋₊ + 1

variable {G : Type*} [AddCommMonoid G]

/-- A corner consists of three points whose coordinate sums agree. -/
structure IsCorner (A : Set (G × G)) (x₁ y₁ x₂ y₂ : G) : Prop where
  fst_fst_mem : (x₁, y₁) ∈ A
  fst_snd_mem : (x₁, y₂) ∈ A
  snd_fst_mem : (x₂, y₁) ∈ A
  add_eq_add : x₁ + y₂ = x₂ + y₁

/-- A set is corner-free when every corner in it has zero displacement. -/
def IsCornerFree (A : Set (G × G)) : Prop :=
  ∀ ⦃x₁ y₁ x₂ y₂⦄, IsCorner A x₁ y₁ x₂ y₂ → x₁ = x₂

open Fin.NatCast in
/-- The corners theorem for finite subsets of an initial square in `ℕ × ℕ`. -/
theorem corners_theorem_nat (hε : 0 < ε) (hn : cornersTheoremBound (ε / 9) ≤ n)
    (A : Finset (ℕ × ℕ)) (hAn : A ⊆ range n ×ˢ range n) (hAε : ε * n ^ 2 ≤ #A) :
    ¬ IsCornerFree (A : Set (ℕ × ℕ)) := sorry

end Q5171652
