/-
Copyright (c) 2022 Jeoff Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeoff Lee, Thomas Zhu
-/
import Mathlib.Tactic.LinearCombination
import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots

/-!
# The roots of cubic and quartic polynomials

This file proves Theorem 37 and 46 from the [100 Theorems List](https://www.cs.ru.nl/~freek/100/).

We give the solutions to the cubic equation `a * x^3 + b * x^2 + c * x + d = 0` over a field `K`
that has characteristic neither 2 nor 3, that has a third primitive root of
unity, and in which certain other quantities admit square and cube roots. This is based on the
[Cardano's Formula](https://en.wikipedia.org/wiki/Cubic_equation#Cardano's_formula).

We also give solutions to the quartic equation `a * x^4 + b * x^3 + c * x^2 + d * x + e = 0` over
a field `K` that is not characteristic 2, and in which certain quantities admit square roots, in
terms of a quantity that is a root of a particular cubic equation.

## Main statements

- `cubic_eq_zero_iff`: gives the roots of the cubic equation
  where the discriminant `p = 3 * a * c - b^2` is nonzero.
- `cubic_eq_zero_iff_of_p_eq_zero`: gives the roots of the cubic equation
  where the discriminant equals zero.
- `quartic_eq_zero_iff`: gives the roots of the quartic equation
  where the quantity `b^3 - 4 * a * b * c + 8 * a^2 * d` is nonzero, in terms of a root `u`
  to a cubic resolvent.
- `quartic_eq_zero_iff_of_q_eq_zero`: gives the roots of the quartic equation
  where the quantity `b^3 - 4 * a * b * c + 8 * a^2 * d` equals zero.

## Proof outline

Proofs of the cubic and quartic formulas are similar in outline.

For a cubic:
1.  Given cubic $ax^3 + bx^2 + cx + d = 0$, we show it is equivalent to some "depressed cubic"
    $y^3 + 3py - 2q = 0$ where $y = x + b / (3a)$, $p = (3ac - b^2) / (9a^2)$, and
    $q = (9abc - 2b^3 - 27a^2d) / (54a^3)$ (`h₁` in `cubic_eq_zero_iff`).
2.  When $p$ is zero, this is easily solved (`cubic_eq_zero_iff_of_p_eq_zero`).
3.  Otherwise one can directly derive a factorization of the depressed cubic, in terms of some
    primitive cube root of unity $\omega^3 = 1$ (`cubic_depressed_eq_zero_iff`).

Similarly, for a quartic:
1.  Given quartic $ax^4 + bx^3 + cx^2 + dx + e = 0$, it is equivalent to some "depressed quartic"
    $y^4 + py^2 + qy + r = 0$ where $y = x + b / (4a)$, $p = (8ac - 3b^2) / (8a^2))$,
    $q = b^3 - 4abc + 8a^2d) / (8a^3))$, and $r = (16ab^2c + 256a^3e - 3b^4 - 64a^2bd) / (256a^4)$
    (`h₁` in `quartic_eq_zero_iff`).
2.  When $q$ is zero, this is easily solved as a quadratic in $y^2$
    (`quartic_eq_zero_iff_of_q_eq_zero`).
3.  Otherwise one can directly derive a factorization of the depressed quartic into two quadratics,
    in terms of some root of the *cubic resolvent* $u^3 - pu^2 - 4ru + 4pr - q^2 = 0$
    (`quartic_depressed_eq_zero_iff`).

## References

The cubic formula was originally ported from Isabelle/HOL. The
[original file](https://isabelle.in.tum.de/dist/library/HOL/HOL-ex/Cubic_Quartic.html) was written by Amine Chaieb.

The proof of the quartic formula is similar in structure to the cubic, and uses the formulation in
[Zwillinger, *CRC Standard Mathematical Tables and Formulae*](zwillinger2003).

## Tags

polynomial, cubic, quartic, root
-/


namespace Theorems100

section Field

open Polynomial

variable {K : Type*} [Field K] (a b c d e : K) {ω p q r s t u v w x y : K}

section Cubic

theorem cube_root_of_unity_sum (hω : IsPrimitiveRoot ω 3) : 1 + ω + ω ^ 2 = 0 := by sorry
theorem cubic_depressed_eq_zero_iff (hω : IsPrimitiveRoot ω 3) (hp_nonzero : p ≠ 0)
    (hr : r ^ 2 = q ^ 2 + p ^ 3) (hs3 : s ^ 3 = q + r) (ht : t * s = p) (x : K) :
    x ^ 3 + 3 * p * x - 2 * q = 0 ↔ x = s - t ∨ x = s * ω - t * ω ^ 2 ∨ x = s * ω ^ 2 - t * ω := by sorry
variable [Invertible (2 : K)] [Invertible (3 : K)]

/-- **The Solution of Cubic**.
  The roots of a cubic polynomial whose discriminant is nonzero. -/
theorem cubic_eq_zero_iff (ha : a ≠ 0) (hω : IsPrimitiveRoot ω 3)
    (hp : p = (3 * a * c - b ^ 2) / (9 * a ^ 2)) (hp_nonzero : p ≠ 0)
    (hq : q = (9 * a * b * c - 2 * b ^ 3 - 27 * a ^ 2 * d) / (54 * a ^ 3))
    (hr : r ^ 2 = q ^ 2 + p ^ 3) (hs3 : s ^ 3 = q + r) (ht : t * s = p) (x : K) :
    a * x ^ 3 + b * x ^ 2 + c * x + d = 0 ↔
      x = s - t - b / (3 * a) ∨
        x = s * ω - t * ω ^ 2 - b / (3 * a) ∨ x = s * ω ^ 2 - t * ω - b / (3 * a) := by sorry
theorem cubic_eq_zero_iff_of_p_eq_zero (ha : a ≠ 0) (hω : IsPrimitiveRoot ω 3)
    (hpz : 3 * a * c - b ^ 2 = 0)
    (hq : q = (9 * a * b * c - 2 * b ^ 3 - 27 * a ^ 2 * d) / (54 * a ^ 3)) (hs3 : s ^ 3 = 2 * q)
    (x : K) :
    a * x ^ 3 + b * x ^ 2 + c * x + d = 0 ↔
      x = s - b / (3 * a) ∨ x = s * ω - b / (3 * a) ∨ x = s * ω ^ 2 - b / (3 * a) := by sorry
end Cubic

section Quartic

variable [Invertible (2 : K)]

/-- Roots of a quartic whose cubic term is zero and linear term is nonzero,
  In terms of some `u` that satisfies a particular cubic resolvent. -/
theorem quartic_depressed_eq_zero_iff
    (hq_nonzero : q ≠ 0)
    (hu : u ^ 3 - p * u ^ 2 - 4 * r * u + 4 * p * r - q ^ 2 = 0)
    (hs : s ^ 2 = u - p)
    (hv : v ^ 2 = 4 * s ^ 2 - 8 * (u - q / s))
    (hw : w ^ 2 = 4 * s ^ 2 - 8 * (u + q / s))
    (x : K) :
    x ^ 4 + p * x ^ 2 + q * x + r = 0 ↔
      x = (-2 * s - v) / 4 ∨ x = (-2 * s + v) / 4 ∨ x = (2 * s - w) / 4 ∨ x = (2 * s + w) / 4 := by sorry
theorem quartic_eq_zero_iff (ha : a ≠ 0)
    (hp : p = (8 * a * c - 3 * b ^ 2) / (8 * a ^ 2))
    (hq : q = (b ^ 3 - 4 * a * b * c + 8 * a ^ 2 * d) / (8 * a ^ 3)) (hq_nonzero : q ≠ 0)
    (hr : r =
      (16 * a * b ^ 2 * c + 256 * a ^ 3 * e - 3 * b ^ 4 - 64 * a ^ 2 * b * d) / (256 * a ^ 4))
    (hu : u ^ 3 - p * u ^ 2 - 4 * r * u + 4 * p * r - q ^ 2 = 0)
    (hs : s ^ 2 = u - p)
    (hv : v ^ 2 = 4 * s ^ 2 - 8 * (u - q / s))
    (hw : w ^ 2 = 4 * s ^ 2 - 8 * (u + q / s)) (x : K) :
    a * x ^ 4 + b * x ^ 3 + c * x ^ 2 + d * x + e = 0 ↔
      x = (-2 * s - v) / 4 - b / (4 * a) ∨ x = (-2 * s + v) / 4 - b / (4 * a) ∨
        x = (2 * s - w) / 4 - b / (4 * a) ∨ x = (2 * s + w) / 4 - b / (4 * a) := by sorry
theorem quartic_eq_zero_iff_of_q_eq_zero (ha : a ≠ 0)
    (hp : p = (8 * a * c - 3 * b ^ 2) / (8 * a ^ 2))
    (hqz : b ^ 3 - 4 * a * b * c + 8 * a ^ 2 * d = 0)
    (hr : r =
      (16 * a * b ^ 2 * c + 256 * a ^ 3 * e - 3 * b ^ 4 - 64 * a ^ 2 * b * d) / (256 * a ^ 4))
    (ht : t ^ 2 = p ^ 2 - 4 * r)
    (hv : v ^ 2 = (-p + t) / 2)
    (hw : w ^ 2 = (-p - t) / 2) (x : K) :
    a * x ^ 4 + b * x ^ 3 + c * x ^ 2 + d * x + e = 0 ↔
      x = v - b / (4 * a) ∨ x = -v - b / (4 * a) ∨ x = w - b / (4 * a) ∨ x = -w - b / (4 * a) := by sorry
end Quartic

end Field

end Theorems100
