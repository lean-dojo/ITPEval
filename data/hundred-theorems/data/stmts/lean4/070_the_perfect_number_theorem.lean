/-
Copyright (c) 2020 Aaron Anderson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson
-/
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.Tactic.NormNum.Prime

/-!
# Perfect Numbers

This file proves Theorem 70 from the [100 Theorems List](https://www.cs.ru.nl/~freek/100/).

The theorem characterizes even perfect numbers.

Euclid proved that if `2 ^ (k + 1) - 1` is prime (these primes are known as Mersenne primes),
  then `2 ^ k * (2 ^ (k + 1) - 1)` is perfect.

Euler proved the converse, that if `n` is even and perfect, then there exists `k` such that
  `n = 2 ^ k * (2 ^ (k + 1) - 1)` and `2 ^ (k + 1) - 1` is prime.

## References
https://en.wikipedia.org/wiki/Euclid%E2%80%93Euler_theorem
-/


namespace Theorems100

namespace Nat

open ArithmeticFunction Finset

-- access notation `σ`
open scoped sigma

theorem sigma_two_pow_eq_mersenne_succ (k : ℕ) : σ 1 (2 ^ k) = mersenne (k + 1) := by sorry
theorem perfect_two_pow_mul_mersenne_of_prime (k : ℕ) (pr : (mersenne (k + 1)).Prime) :
    Nat.Perfect (2 ^ k * mersenne (k + 1)) := by sorry
theorem ne_zero_of_prime_mersenne (k : ℕ) (pr : (mersenne (k + 1)).Prime) : k ≠ 0 := by sorry
theorem even_two_pow_mul_mersenne_of_prime (k : ℕ) (pr : (mersenne (k + 1)).Prime) :
    Even (2 ^ k * mersenne (k + 1)) := by simp [ne_zero_of_prime_mersenne k pr, parity_simps]

theorem eq_two_pow_mul_odd {n : ℕ} (hpos : 0 < n) : ∃ k m : ℕ, n = 2 ^ k * m ∧ ¬Even m := by sorry
theorem eq_two_pow_mul_prime_mersenne_of_even_perfect {n : ℕ} (ev : Even n) (perf : Nat.Perfect n) :
    ∃ k : ℕ, Nat.Prime (mersenne (k + 1)) ∧ n = 2 ^ k * mersenne (k + 1) := by sorry
theorem even_and_perfect_iff {n : ℕ} :
    Even n ∧ Nat.Perfect n ↔ ∃ k : ℕ, Nat.Prime (mersenne (k + 1)) ∧
      n = 2 ^ k * mersenne (k + 1) := by sorry
end Nat

end Theorems100
