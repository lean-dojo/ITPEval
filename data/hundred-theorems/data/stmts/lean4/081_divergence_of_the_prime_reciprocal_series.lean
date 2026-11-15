/-
Copyright (c) 2021 Manuel Candales. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Manuel Candales
-/
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Data.Nat.Cast.Order.Field
import Mathlib.Data.Nat.Squarefree

/-!
# Divergence of the Prime Reciprocal Series

This file proves Theorem 81 from the [100 Theorems List](https://www.cs.ru.nl/~freek/100/).
The theorem states that the sum of the reciprocals of all prime numbers diverges.
The formalization follows Erdős's proof by upper and lower estimates.

## Proof outline

1. Assume that the sum of the reciprocals of the primes converges.
2. Then there exists a `k : ℕ` such that, for any `x : ℕ`, the sum of the reciprocals of the primes
   between `k` and `x + 1` is less than 1/2 (`sum_lt_half_of_not_tendsto`).
3. For any `x : ℕ`, we can partition `range x` into two subsets (`range_sdiff_eq_biUnion`):
    * `M x k`, the subset of those `e` for which `e + 1` is a product of powers of primes smaller
      than or equal to `k`;
    * `U x k`, the subset of those `e` for which there is a prime `p > k` that divides `e + 1`.
4. Then `|U x k|` is bounded by the sum over the primes `p > k` of the number of multiples of `p`
   in `(k, x]`, which is at most `x / p`. It follows that `|U x k|` is at most `x` times the sum of
   the reciprocals of the primes between `k` and `x + 1`, which is less than 1/2 as noted in (2), so
   `|U x k| < x / 2` (`card_le_mul_sum`).
5. By factoring `e + 1 = (m + 1)² * (r + 1)`, `r + 1` squarefree and `m + 1 ≤ √x`, and noting that
   squarefree numbers correspond to subsets of `[1, k]`, we find that `|M x k| ≤ 2 ^ k * √x`
   (`card_le_two_pow_mul_sqrt`).
6. Finally, setting `x := (2 ^ (k + 1))²` (`√x = 2 ^ (k + 1)`), we find that
   `|M x k| ≤ 2 ^ k * 2 ^ (k + 1) = x / 2`. Combined with the strict bound for `|U k x|` from (4),
   `x = |M x k| + |U x k| < x / 2 + x / 2 = x`.

## References

https://en.wikipedia.org/wiki/Divergence_of_the_sum_of_the_reciprocals_of_the_primes
-/

open Filter Finset

namespace Theorems100

/-- The primes in `(k, x]`.
-/
def P (x k : ℕ) : Finset ℕ := {p ∈ range (x + 1) | k < p ∧ p.Prime}

/-- The union over those primes `p ∈ (k, x]` of the sets of `e < x` for which `e + 1` is a multiple
of `p`, i.e., those `e < x` for which there is a prime `p ∈ (k, x]` that divides `e + 1`.
-/
def U (x k : ℕ) : Finset ℕ := (P x k).biUnion fun p ↦ {e ∈ range x | p ∣ e + 1}

open Classical in
/-- Those `e < x` for which `e + 1` is a product of powers of primes smaller than or equal to `k`.
-/
noncomputable def M (x k : ℕ) : Finset ℕ := {e ∈ range x | ∀ p : ℕ, p.Prime ∧ p ∣ e + 1 → p ≤ k}

/--
If the sum of the reciprocals of the primes converges, there exists a `k : ℕ` such that the sum of
the reciprocals of the primes greater than `k` is less than 1/2.

More precisely, for any `x : ℕ`, the sum of the reciprocals of the primes between `k` and `x + 1`
is less than 1/2.
-/
theorem sum_lt_half_of_not_tendsto
    (h : ¬Tendsto (fun n => ∑ p ∈ range n with p.Prime, 1 / (p : ℝ))
      atTop atTop) :
    ∃ k, ∀ x, ∑ p ∈ P x k, 1 / (p : ℝ) < 1 / 2 := by sorry
theorem range_sdiff_eq_biUnion {x k : ℕ} : range x \ M x k = U x k := by sorry
theorem card_le_mul_sum {x k : ℕ} : #(U x k) ≤ x * ∑ p ∈ P x k, 1 / (p : ℝ) := by sorry
theorem card_le_two_pow {x k : ℕ} : #{e ∈ M x k | Squarefree (e + 1)} ≤ 2 ^ k := by sorry
    #M₁ ≤ #(image f K) := card_le_card h
    _ ≤ #K := card_image_le
    _ ≤ 2 ^ #(image Nat.succ (range k)) := by simp only [K, card_powerset]; rfl
    _ ≤ 2 ^ #(range k) := pow_right_mono₀ one_le_two card_image_le
    _ = 2 ^ k := by rw [card_range k]

/--
The number of `e < x` for which `e + 1` is a product of powers of primes smaller than or equal to
`k` is bounded by `2 ^ k * nat.sqrt x`.
-/
theorem card_le_two_pow_mul_sqrt {x k : ℕ} : #(M x k) ≤ 2 ^ k * Nat.sqrt x := by sorry
theorem Real.tendsto_sum_one_div_prime_atTop :
    Tendsto (fun n => ∑ p ∈ range n with p.Prime, 1 / (p : ℝ))
      atTop atTop := by sorry
end Theorems100
