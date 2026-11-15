/-
Copyright (c) 2025 Alex Meiburg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Meiburg
-/
module

public import Mathlib.Algebra.Polynomial.CoeffList
public import Mathlib.Algebra.Polynomial.Monic
public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.Data.List.Destutter
public import Mathlib.Data.Sign.Basic

/-!

# Descartes' Rule of Signs

We define the "sign changes" in the coefficients of a polynomial, and prove Descartes'
Rule of Signs: a real polynomial has at most as many positive roots as there are sign
changes. A sign change is when there is a positive coefficient followed by a negative
coefficient, or vice versa, with any number of zero coefficients in between.

## Main Definitions

- `Polynomial.signVariations`: The number of sign changes in a polynomial's coefficients,
  where `0` coefficients are ignored.

## Main theorem

- `Polynomial.roots_countP_pos_le_signVariations`. States that
  `P.roots.countP (0 < ·) ≤ P.signVariations`, so that positive roots are counted with multiplicity.
  It's currently proved for any `CommRing` with `IsStrictOrderedRing`. There is likely some correct
  statement in terms of a (noncommutative) `Ring`, but `Polynomial.roots` is only defined for
  commutative rings.

## Reference

[Wikipedia: Descartes' Rule of Signs](https://en.wikipedia.org/wiki/Descartes%27_rule_of_signs)
-/

@[expose] public section

namespace Polynomial

section Semiring
variable {R : Type*} [Semiring R] [LinearOrder R] (P : Polynomial R)

/-- Counts the number of times that the coefficients in a polynomial change sign, with
the convention that 0 can count as either sign. -/
def signVariations : ℕ :=
  letI coeff_signs := (coeffList P).map SignType.sign
  letI nonzero_signs := coeff_signs.filter (· ≠ 0)
  (nonzero_signs.destutter (· ≠ ·)).length - 1

variable (R) in
@[simp]
theorem signVariations_zero : signVariations (0 : R[X]) = 0 := by sorry
theorem signVariations_monomial (d : ℕ) (c : R) : signVariations (monomial d c) = 0 := by sorry
theorem signVariations_eraseLead (h : SignType.sign P.leadingCoeff = SignType.sign P.nextCoeff) :
    signVariations P.eraseLead = signVariations P := by sorry
theorem signVariations_eq_eraseLead_add_ite {P : Polynomial R} (h : P ≠ 0) :
    signVariations P = signVariations P.eraseLead + if SignType.sign P.leadingCoeff
      = -SignType.sign P.eraseLead.leadingCoeff then 1 else 0 := by sorry
theorem signVariations_eraseLead_le : signVariations P.eraseLead ≤ signVariations P := by sorry
theorem signVariations_le_eraseLead_succ : signVariations P ≤ signVariations P.eraseLead + 1 := by sorry
end Semiring

section OrderedRing

variable {R : Type*} [Ring R] [LinearOrder R] [IsOrderedRing R] (P : Polynomial R) {x : R}

/-- The number of sign changes does not change if we negate. -/
@[simp]
theorem signVariations_neg : signVariations (-P) = signVariations P := by sorry
end OrderedRing

section StrictOrderedRing

variable {R : Type*} [Ring R] [LinearOrder R] [IsStrictOrderedRing R] {P : Polynomial R} {η : R}

/-- The number of sign changes does not change if we multiply by any nonzero scalar. -/
@[simp]
theorem signVariations_C_mul (P : Polynomial R) (hx : η ≠ 0) :
    signVariations (C η * P) = signVariations P := by sorry
lemma signVariations_eraseLead_mul_X_sub_C (hη : 0 < η) (hP₀ : 0 < leadingCoeff P)
    (hc : P.nextCoeff < 0) :
    ((X - C η) * P).eraseLead.signVariations = ((X - C η) * P.eraseLead).signVariations := by sorry
lemma succ_signVariations_X_sub_C_mul_monomial {d c} (hc : c ≠ 0) (hη : 0 < η) :
    (monomial d c).signVariations + 1 ≤ ((X - C η) * monomial d c).signVariations := by sorry
        #adaptation_note
        /--
        Moving from `nightly-2025-10-13` to `nightly-2025-10-19`
        we now need to provide an intermediate step.
        -/
        have : ((X - C η) * P).natDegree - ((X - C η) * P).eraseLead.degree.succ = n + 1 := by grind
        grind [leadingCoeff_mul, leadingCoeff_X_sub_C]
      suffices C η * monomial P.natDegree P.leadingCoeff = monomial P.natDegree P.nextCoeff by
        grind [X_mul_monomial, sub_mul, mul_sub, self_sub_monomial_natDegree_leadingCoeff]
      grind [leadingCoeff, nextCoeff_of_natDegree_pos, eq_of_sub_eq_zero, coeff_X_sub_C_mul]
    · suffices ((X - C η) * P).eraseLead.eraseLead = ((X - C η) * P.eraseLead).eraseLead by
        have := leadingCoeff_cons_eraseLead h₉
        have := coeffList_eraseLead (mt nextCoeff_eq_zero_of_eraseLead_eq_zero h₉)
        grind [leadingCoeff_eraseLead_eq_nextCoeff]
      suffices monomial P.natDegree ((X - C η) * P).nextCoeff =
          monomial P.natDegree P.nextCoeff - C η * monomial P.natDegree P.leadingCoeff by
        grind [X_mul_monomial, sub_mul, mul_sub, self_sub_monomial_natDegree_leadingCoeff,
          natDegree_eraseLead_add_one, leadingCoeff_eraseLead_eq_nextCoeff]
      grind [coeff_X_sub_C_mul, nextCoeff_of_natDegree_pos, leadingCoeff]
  · rw [h_cons, leadingCoeff_mul, leadingCoeff_X_sub_C, one_mul, h₂]

/-- If a polynomial starts with two positive coefficients, then the sign changes in the product
`(X - η) * P` is the same as `(X - η) * P.eraseLead`. This lemma lets us do induction on the
degree of P when P starts with matching coefficient signs. Of course this is also true when the
first two coefficients of P are *negative*, but we just prove the case where they're positive
since it's cleaner and sufficient for the later use. -/
lemma signVariations_X_sub_C_mul_eraseLead_le (h : 0 < P.leadingCoeff) (h₂ : 0 < P.nextCoeff) :
    signVariations ((X - C η) * P.eraseLead) ≤ signVariations ((X - C η) * P) := by sorry
theorem succ_signVariations_le_X_sub_C_mul (hη : 0 < η) (hP : P ≠ 0) :
    signVariations P + 1 ≤ signVariations ((X - C η) * P) := by sorry
end StrictOrderedRing
section CommStrictOrderedRing

variable {R : Type*} [CommRing R] [LinearOrder R] [IsStrictOrderedRing R] (P : Polynomial R)

/-- **Descartes' Rule of Signs**: the number of positive roots is at most the number of sign
variations. -/
theorem roots_countP_pos_le_signVariations : P.roots.countP (0 < ·) ≤ signVariations P := by sorry
end CommStrictOrderedRing
end Polynomial
