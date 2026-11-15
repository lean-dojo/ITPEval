/-
Copyright (c) 2020 Patrick Stevens. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Stevens, Bolton Bailey
-/
module

public import Mathlib.Data.Nat.Choose.Factorization
public import Mathlib.NumberTheory.Primorial
public import Mathlib.Analysis.Convex.SpecificFunctions.Basic
public import Mathlib.Analysis.Convex.SpecificFunctions.Deriv
public import Mathlib.Tactic.NormNum.Prime

/-!
# Bertrand's Postulate

This file contains a proof of Bertrand's postulate: That between any positive number and its
double there is a prime.

The proof follows the outline of the Erdős proof presented in "Proofs from THE BOOK": One considers
the prime factorization of `(2 * n).choose n`, and splits the constituent primes up into various
groups, then upper bounds the contribution of each group. This upper bounds the central binomial
coefficient, and if the postulate does not hold, this upper bound conflicts with a simple lower
bound for large enough `n`. This proves the result holds for large enough `n`, and for smaller `n`
an explicit list of primes is provided which covers the remaining cases.

As in the [Metamath implementation](carneiro2015arithmetic), we rely on some optimizations from
[Shigenori Tochiori](tochiori_bertrand). In particular we use the cleaner bound on the central
binomial coefficient given in `Nat.four_pow_lt_mul_centralBinom`.

## References

* [M. Aigner and G. M. Ziegler _Proofs from THE BOOK_][aigner1999proofs]
* [S. Tochiori, _Considering the Proof of “There is a Prime between n and 2n”_][tochiori_bertrand]
* [M. Carneiro, _Arithmetic in Metamath, Case Study: Bertrand's Postulate_][carneiro2015arithmetic]

## Tags

Bertrand, prime, binomial coefficients
-/

public section


section Real

open Real

namespace Bertrand

/-- A refined version of the `Bertrand.main_inequality` below.
This is not best possible: it actually holds for 464 ≤ x.
-/
theorem real_main_inequality {x : ℝ} (x_large : (512 : ℝ) ≤ x) :
    x * (2 * x) ^ √(2 * x) * 4 ^ (2 * x / 3) ≤ 4 ^ x := by sorry
end Bertrand

end Real

section Nat

open Nat

/-- The inequality which contradicts Bertrand's postulate, for large enough `n`.
-/
theorem bertrand_main_inequality {n : ℕ} (n_large : 512 ≤ n) :
    n * (2 * n) ^ sqrt (2 * n) * 4 ^ (2 * n / 3) ≤ 4 ^ n := by sorry
theorem centralBinom_factorization_small (n : ℕ) (n_large : 2 < n)
    (no_prime : ∀ p : ℕ, p.Prime → n < p → 2 * n < p) :
    centralBinom n = ∏ p ∈ Finset.range (2 * n / 3 + 1), p ^ (centralBinom n).factorization p := by sorry
theorem centralBinom_le_of_no_bertrand_prime (n : ℕ) (n_large : 2 < n)
    (no_prime : ∀ p : ℕ, p.Prime → n < p → 2 * n < p) :
    centralBinom n ≤ (2 * n) ^ sqrt (2 * n) * 4 ^ (2 * n / 3) := by sorry
namespace Nat

/-- Proves that **Bertrand's postulate** holds for all sufficiently large `n`.
-/
theorem exists_prime_lt_and_le_two_mul_eventually (n : ℕ) (n_large : 512 ≤ n) :
    ∃ p : ℕ, p.Prime ∧ n < p ∧ p ≤ 2 * n := by sorry
theorem exists_prime_lt_and_le_two_mul_succ {n} (q) {p : ℕ} (prime_p : Nat.Prime p)
    (covering : p ≤ 2 * q) (H : n < q → ∃ p : ℕ, p.Prime ∧ n < p ∧ p ≤ 2 * n) (hn : n < p) :
    ∃ p : ℕ, p.Prime ∧ n < p ∧ p ≤ 2 * n := by sorry
theorem exists_prime_lt_and_le_two_mul (n : ℕ) (hn0 : n ≠ 0) :
    ∃ p, Nat.Prime p ∧ n < p ∧ p ≤ 2 * n := by sorry
  open Lean Elab Tactic in
  run_tac do
    for i in [317, 163, 83, 43, 23, 13, 7, 5, 3, 2] do
      let i : Term := quote i
      evalTactic <| ←
        `(tactic| refine exists_prime_lt_and_le_two_mul_succ $i (by norm_num1) (by norm_num1) ?_)
  exact fun h2 => ⟨2, prime_two, h2, Nat.mul_le_mul_left 2 (Nat.pos_of_ne_zero hn0)⟩

alias bertrand := Nat.exists_prime_lt_and_le_two_mul

end Nat

end Nat
