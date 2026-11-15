/-
Copyright (c) 2019 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes
-/
module

public import Mathlib.FieldTheory.Finite.Basic

/-!
# Lagrange's four square theorem

The main result in this file is `sum_four_squares`,
a proof that every natural number is the sum of four square numbers.

## Implementation Notes

The proof used is close to Lagrange's original proof.
-/

public section


open Finset Polynomial FiniteField Equiv

/-- **Euler's four-square identity**. -/
theorem euler_four_squares {R : Type*} [CommRing R] (a b c d x y z w : R) :
    (a * x - b * y - c * z - d * w) ^ 2 + (a * y + b * x + c * w - d * z) ^ 2 +
      (a * z - b * w + c * x + d * y) ^ 2 + (a * w + b * z - c * y + d * x) ^ 2 =
      (a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2) * (x ^ 2 + y ^ 2 + z ^ 2 + w ^ 2) := by ring

/-- **Euler's four-square identity**, a version for natural numbers. -/
theorem Nat.euler_four_squares (a b c d x y z w : ℕ) :
    ((a : ℤ) * x - b * y - c * z - d * w).natAbs ^ 2 +
      ((a : ℤ) * y + b * x + c * w - d * z).natAbs ^ 2 +
      ((a : ℤ) * z - b * w + c * x + d * y).natAbs ^ 2 +
      ((a : ℤ) * w + b * z - c * y + d * x).natAbs ^ 2 =
      (a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2) * (x ^ 2 + y ^ 2 + z ^ 2 + w ^ 2) := by sorry
namespace Int

theorem sq_add_sq_of_two_mul_sq_add_sq {m x y : ℤ} (h : 2 * m = x ^ 2 + y ^ 2) :
    m = ((x - y) / 2) ^ 2 + ((x + y) / 2) ^ 2 :=
  have : Even (x ^ 2 + y ^ 2) := by simp [← h]
  mul_right_injective₀ (show (2 * 2 : ℤ) ≠ 0 by decide) <|
    calc
      2 * 2 * m = (x - y) ^ 2 + (x + y) ^ 2 := by rw [mul_assoc, h]; ring
      _ = (2 * ((x - y) / 2)) ^ 2 + (2 * ((x + y) / 2)) ^ 2 := by sorry
theorem lt_of_sum_four_squares_eq_mul {a b c d k m : ℕ}
    (h : a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 = k * m)
    (ha : 2 * a < m) (hb : 2 * b < m) (hc : 2 * c < m) (hd : 2 * d < m) :
    k < m := by nlinarith

theorem exists_sq_add_sq_add_one_eq_mul (p : ℕ) [hp : Fact p.Prime] :
    ∃ (a b k : ℕ), 0 < k ∧ k < p ∧ a ^ 2 + b ^ 2 + 1 = k * p := by sorry
end Int

namespace Nat

open Int

private theorem sum_four_squares_of_two_mul_sum_four_squares {m a b c d : ℤ}
    (h : a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 = 2 * m) :
    ∃ w x y z : ℤ, w ^ 2 + x ^ 2 + y ^ 2 + z ^ 2 = m := by sorry
theorem sum_four_squares (n : ℕ) : ∃ a b c d : ℕ, a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 = n := by sorry
end Nat
