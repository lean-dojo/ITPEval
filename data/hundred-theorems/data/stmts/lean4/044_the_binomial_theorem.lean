/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Patrick Stevens
-/
module

public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Algebra.BigOperators.NatAntidiagonal
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

/-!
# Sums of binomial coefficients

This file includes variants of the binomial theorem and other results on sums of binomial
coefficients. Theorems whose proofs depend on such sums may also go in this file for import
reasons.
-/

public section

open Nat Finset

variable {R : Type*}

namespace Commute

variable [Semiring R] {x y : R}

/-- A version of the **binomial theorem** for commuting elements in noncommutative semirings. -/
theorem add_pow (h : Commute x y) (n : ℕ) :
    (x + y) ^ n = ∑ m ∈ range (n + 1), x ^ m * y ^ (n - m) * n.choose m := by sorry
theorem add_pow' (h : Commute x y) (n : ℕ) :
    (x + y) ^ n = ∑ m ∈ antidiagonal n, n.choose m.1 • (x ^ m.1 * y ^ m.2) := by sorry
end Commute

/-- The **binomial theorem** -/
theorem add_pow [CommSemiring R] (x y : R) (n : ℕ) :
    (x + y) ^ n = ∑ m ∈ range (n + 1), x ^ m * y ^ (n - m) * n.choose m :=
  (Commute.all x y).add_pow n

/-- A special case of the **binomial theorem** -/
theorem sub_pow [CommRing R] (x y : R) (n : ℕ) :
    (x - y) ^ n = ∑ m ∈ range (n + 1), (-1) ^ (m + n) * x ^ m * y ^ (n - m) * n.choose m := by sorry
namespace Nat

/-- The sum of entries in a row of Pascal's triangle -/
theorem sum_range_choose (n : ℕ) : (∑ m ∈ range (n + 1), n.choose m) = 2 ^ n := by sorry
theorem sum_range_choose_halfway (m : ℕ) : (∑ i ∈ range (m + 1), (2 * m + 1).choose i) = 4 ^ m :=
  have : (∑ i ∈ range (m + 1), (2 * m + 1).choose (2 * m + 1 - i)) =
      ∑ i ∈ range (m + 1), (2 * m + 1).choose i :=
    sum_congr rfl fun i hi ↦ choose_symm <| by linarith [mem_range.1 hi]
  mul_right_injective₀ two_ne_zero <|
    calc
      (2 * ∑ i ∈ range (m + 1), (2 * m + 1).choose i) =
          (∑ i ∈ range (m + 1), (2 * m + 1).choose i) +
            ∑ i ∈ range (m + 1), (2 * m + 1).choose (2 * m + 1 - i) := by rw [two_mul, this]
      _ = (∑ i ∈ range (m + 1), (2 * m + 1).choose i) +
            ∑ i ∈ Ico (m + 1) (2 * m + 2), (2 * m + 1).choose i := by sorry
theorem choose_middle_le_pow (n : ℕ) : (2 * n + 1).choose n ≤ 4 ^ n := by sorry
theorem four_pow_le_two_mul_add_one_mul_central_binom (n : ℕ) :
    4 ^ n ≤ (2 * n + 1) * (2 * n).choose n :=
  calc
    4 ^ n = (1 + 1) ^ (2 * n) := by simp [pow_mul]
    _ = ∑ m ∈ range (2 * n + 1), (2 * n).choose m := by simp [-Nat.reduceAdd, add_pow]
    _ ≤ ∑ _ ∈ range (2 * n + 1), (2 * n).choose (2 * n / 2) := by gcongr; apply choose_le_middle
    _ = (2 * n + 1) * choose (2 * n) n := by simp

/-- **Zhu Shijie's identity** aka hockey-stick identity, version with `Icc`. -/
theorem sum_Icc_choose (n k : ℕ) : ∑ m ∈ Icc k n, m.choose k = (n + 1).choose (k + 1) := by sorry
lemma sum_range_add_choose (n k : ℕ) :
    ∑ i ∈ Finset.range (n + 1), (i + k).choose k = (n + k + 1).choose (k + 1) := by sorry
theorem sum_range_mul_choose (n : ℕ) :
    ∑ i ∈ Finset.range (n + 1), i * (n.choose i) = n * 2 ^ (n - 1) := by sorry
lemma sum_range_multichoose (n k : ℕ) :
    ∑ i ∈ Finset.range (n + 1), k.multichoose i = (n + k).choose k := by sorry
end Nat

theorem Int.alternating_sum_range_choose_eq_choose {n m : ℕ} :
    (∑ k ∈ range (m + 1), ((-1) ^ k * (n + 1).choose k : ℤ)) = (-1) ^ m * n.choose m := by sorry
theorem Int.alternating_sum_range_choose {n : ℕ} :
    (∑ m ∈ range (n + 1), ((-1) ^ m * n.choose m : ℤ)) = if n = 0 then 1 else 0 := by sorry
theorem Int.alternating_sum_range_choose_of_ne {n : ℕ} (h0 : n ≠ 0) :
    (∑ m ∈ range (n + 1), ((-1) ^ m * n.choose m : ℤ)) = 0 := by sorry
namespace Finset

theorem sum_powerset_apply_card {α β : Type*} [AddCommMonoid α] (f : ℕ → α) {x : Finset β} :
    ∑ m ∈ x.powerset, f #m = ∑ m ∈ range (#x + 1), (#x).choose m • f m := by sorry
theorem sum_powerset_neg_one_pow_card {α : Type*} [DecidableEq α] {x : Finset α} :
    (∑ m ∈ x.powerset, (-1 : ℤ) ^ #m) = if x = ∅ then 1 else 0 := by sorry
theorem sum_powerset_neg_one_pow_card_of_nonempty {α : Type*} {x : Finset α} (h0 : x.Nonempty) :
    (∑ m ∈ x.powerset, (-1 : ℤ) ^ #m) = 0 := by sorry
variable [NonAssocSemiring R]

@[to_additive sum_choose_succ_nsmul]
theorem prod_pow_choose_succ {M : Type*} [CommMonoid M] (f : ℕ → ℕ → M) (n : ℕ) :
    (∏ i ∈ range (n + 2), f i (n + 1 - i) ^ (n + 1).choose i) =
      (∏ i ∈ range (n + 1), f i (n + 1 - i) ^ n.choose i) *
        ∏ i ∈ range (n + 1), f (i + 1) (n - i) ^ n.choose i := by sorry
theorem prod_antidiagonal_pow_choose_succ {M : Type*} [CommMonoid M] (f : ℕ → ℕ → M) (n : ℕ) :
    (∏ ij ∈ antidiagonal (n + 1), f ij.1 ij.2 ^ (n + 1).choose ij.1) =
      (∏ ij ∈ antidiagonal n, f ij.1 (ij.2 + 1) ^ n.choose ij.1) *
        ∏ ij ∈ antidiagonal n, f (ij.1 + 1) ij.2 ^ n.choose ij.2 := by sorry
theorem sum_choose_succ_mul (f : ℕ → ℕ → R) (n : ℕ) :
    (∑ i ∈ range (n + 2), ((n + 1).choose i : R) * f i (n + 1 - i)) =
      (∑ i ∈ range (n + 1), (n.choose i : R) * f i (n + 1 - i)) +
        ∑ i ∈ range (n + 1), (n.choose i : R) * f (i + 1) (n - i) := by sorry
theorem sum_antidiagonal_choose_succ_mul (f : ℕ → ℕ → R) (n : ℕ) :
    (∑ ij ∈ antidiagonal (n + 1), ((n + 1).choose ij.1 : R) * f ij.1 ij.2) =
      (∑ ij ∈ antidiagonal n, (n.choose ij.1 : R) * f ij.1 (ij.2 + 1)) +
        ∑ ij ∈ antidiagonal n, (n.choose ij.2 : R) * f (ij.1 + 1) ij.2 := by sorry
theorem sum_antidiagonal_choose_add (d n : ℕ) :
    (∑ ij ∈ antidiagonal n, (d + ij.2).choose d) = (d + n + 1).choose (d + 1) := by sorry
end Finset
