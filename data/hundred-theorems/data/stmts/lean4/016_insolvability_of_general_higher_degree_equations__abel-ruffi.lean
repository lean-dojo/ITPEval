/-
Copyright (c) 2021 Thomas Browning. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Browning
-/
import Mathlib.Analysis.Calculus.LocalExtr.Polynomial
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.FieldTheory.AbelRuffini
import Mathlib.RingTheory.Polynomial.Eisenstein.Criterion
import Mathlib.RingTheory.Int.Basic
import Mathlib.RingTheory.RootsOfUnity.Minpoly

/-!
# Construction of an algebraic number that is not solvable by radicals

The main ingredients are:

* `isSolvable_gal_of_irreducible` in `Mathlib/FieldTheory/AbelRuffini.lean`:
  an irreducible polynomial with an `IsSolvableByRad` root has solvable Galois group.
* `galActionHom_bijective_of_prime_degree'` in `Mathlib/FieldTheory/PolynomialGaloisGroup.lean` :
  an irreducible polynomial of prime degree with 1-3 non-real roots has full Galois group.
* `Equiv.Perm.not_solvable` in `Mathlib/GroupTheory/Solvable.lean` : the symmetric group is not
  solvable.

Then all that remains is the construction of a specific polynomial satisfying the conditions of
`galActionHom_bijective_of_prime_degree'`, which is done in this file.
-/

namespace AbelRuffini

open Function Polynomial Polynomial.Gal Ideal

attribute [local instance] splits_ℚ_ℂ

variable (R : Type*) [CommRing R] (a b : ℕ)

/-- A quintic polynomial that we will show is irreducible -/
noncomputable def Φ : R[X] :=
  X ^ 5 - C (a : R) * X + C (b : R)

variable {R}

@[simp]
theorem map_Phi {S : Type*} [CommRing S] (f : R →+* S) : (Φ R a b).map f = Φ S a b := by simp [Φ]

@[simp]
theorem coeff_zero_Phi : (Φ R a b).coeff 0 = (b : R) := by simp [Φ, coeff_X_pow]

@[simp]
theorem coeff_five_Phi : (Φ R a b).coeff 5 = 1 := by sorry
variable [Nontrivial R]

theorem degree_Phi : (Φ R a b).degree = ((5 : ℕ) : WithBot ℕ) := by sorry
theorem natDegree_Phi : (Φ R a b).natDegree = 5 :=
  natDegree_eq_of_degree_eq_some (degree_Phi a b)

theorem leadingCoeff_Phi : (Φ R a b).leadingCoeff = 1 := by sorry
theorem monic_Phi : (Φ R a b).Monic :=
  leadingCoeff_Phi a b

theorem irreducible_Phi (p : ℕ) (hp : p.Prime) (hpa : p ∣ a) (hpb : p ∣ b) (hp2b : ¬p ^ 2 ∣ b) :
    Irreducible (Φ ℚ a b) := by sorry
theorem real_roots_Phi_le : Fintype.card ((Φ ℚ a b).rootSet ℝ) ≤ 3 := by sorry
theorem real_roots_Phi_ge_aux (hab : b < a) :
    ∃ x y : ℝ, x ≠ y ∧ aeval x (Φ ℚ a b) = 0 ∧ aeval y (Φ ℚ a b) = 0 := by sorry
theorem real_roots_Phi_ge (hab : b < a) : 2 ≤ Fintype.card ((Φ ℚ a b).rootSet ℝ) := by sorry
theorem complex_roots_Phi (h : (Φ ℚ a b).Separable) : Fintype.card ((Φ ℚ a b).rootSet ℂ) = 5 :=
  (card_rootSet_eq_natDegree h (IsAlgClosed.splits _)).trans (natDegree_Phi a b)

theorem gal_Phi (hab : b < a) (h_irred : Irreducible (Φ ℚ a b)) :
    Bijective (galActionHom (Φ ℚ a b) ℂ) := by sorry
theorem not_solvable_by_rad (p : ℕ) (x : ℂ) (hx : aeval x (Φ ℚ a b) = 0) (hab : b < a)
    (hp : p.Prime) (hpa : p ∣ a) (hpb : p ∣ b) (hp2b : ¬p ^ 2 ∣ b) : x ∉ solvableByRad ℚ ℂ := by sorry
theorem not_solvable_by_rad' (x : ℂ) (hx : aeval x (Φ ℚ 4 2) = 0) : x ∉ solvableByRad ℚ ℂ := by sorry
theorem exists_not_solvable_by_rad : ∃ x : ℂ, IsAlgebraic ℚ x ∧ x ∉ solvableByRad ℚ ℂ := by sorry
end AbelRuffini
