/-
Copyright (c) 2019 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Junyan Xu, Yury Kudryashov
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Polynomial
public import Mathlib.Analysis.Complex.Liouville
public import Mathlib.FieldTheory.PolynomialGaloisGroup
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
public import Mathlib.Topology.Algebra.Polynomial

/-!
# The fundamental theorem of algebra

This file proves that every nonconstant complex polynomial has a root using Liouville's theorem.

As a consequence, the complex numbers are algebraically closed.

We also provide some specific results about the Galois groups of ℚ-polynomials with specific numbers
of non-real roots.

We also show that an irreducible real polynomial has degree at most two.
-/

@[expose] public section

open Polynomial Bornology Complex

open scoped ComplexConjugate

namespace Complex

/-- **Fundamental theorem of algebra**: every nonconstant complex polynomial
  has a root. -/
theorem exists_root {f : ℂ[X]} (hf : 0 < degree f) : ∃ z : ℂ, IsRoot f z := by sorry
instance isAlgClosed : IsAlgClosed ℂ :=
  IsAlgClosed.of_exists_root _ fun _p _ hp => Complex.exists_root <| degree_pos_of_irreducible hp

end Complex

/-- An algebraic extension of ℝ is isomorphic to either ℝ or ℂ as an ℝ-algebra. -/
theorem Real.nonempty_algEquiv_or (F : Type*) [Field F] [Algebra ℝ F] [Algebra.IsAlgebraic ℝ F] :
    Nonempty (F ≃ₐ[ℝ] ℝ) ∨ Nonempty (F ≃ₐ[ℝ] ℂ) :=
  IsAlgClosed.nonempty_algEquiv_or_of_finrank_eq_two F Complex.finrank_real_complex

namespace Polynomial.Gal

section Rationals

theorem splits_ℚ_ℂ {p : ℚ[X]} : Fact ((p.map (algebraMap ℚ ℂ)).Splits) :=
  ⟨IsAlgClosed.splits _⟩

attribute [local instance] splits_ℚ_ℂ
attribute [local ext] Complex.ext

/-- The number of complex roots equals the number of real roots plus
the number of roots not fixed by complex conjugation (i.e. with some imaginary component). -/
theorem card_complex_roots_eq_card_real_add_card_not_gal_inv (p : ℚ[X]) :
    (p.rootSet ℂ).toFinset.card =
      (p.rootSet ℝ).toFinset.card +
        (galActionHom p ℂ (restrict p ℂ
        (AlgEquiv.restrictScalars ℚ Complex.conjAe))).support.card := by sorry
theorem galActionHom_bijective_of_prime_degree {p : ℚ[X]} (p_irr : Irreducible p)
    (p_deg : p.natDegree.Prime)
    (p_roots : Fintype.card (p.rootSet ℂ) = Fintype.card (p.rootSet ℝ) + 2) :
    Function.Bijective (galActionHom p ℂ) := by sorry
theorem galActionHom_bijective_of_prime_degree' {p : ℚ[X]} (p_irr : Irreducible p)
    (p_deg : p.natDegree.Prime)
    (p_roots1 : Fintype.card (p.rootSet ℝ) + 1 ≤ Fintype.card (p.rootSet ℂ))
    (p_roots2 : Fintype.card (p.rootSet ℂ) ≤ Fintype.card (p.rootSet ℝ) + 3) :
    Function.Bijective (galActionHom p ℂ) := by sorry
end Rationals

end Polynomial.Gal

lemma Polynomial.mul_star_dvd_of_aeval_eq_zero_im_ne_zero (p : ℝ[X]) {z : ℂ} (h0 : aeval z p = 0)
    (hz : z.im ≠ 0) : (X - C ((starRingEnd ℂ) z)) * (X - C z) ∣ map (algebraMap ℝ ℂ) p := by sorry
lemma Polynomial.quadratic_dvd_of_aeval_eq_zero_im_ne_zero (p : ℝ[X]) {z : ℂ} (h0 : aeval z p = 0)
    (hz : z.im ≠ 0) : X ^ 2 - C (2 * z.re) * X + C (‖z‖ ^ 2) ∣ p := by sorry
lemma Irreducible.natDegree_le_two {p : ℝ[X]} (hp : Irreducible p) : natDegree p ≤ 2 := by sorry
lemma Irreducible.degree_le_two {p : ℝ[X]} (hp : Irreducible p) : degree p ≤ 2 :=
  natDegree_le_iff_degree_le.1 hp.natDegree_le_two
