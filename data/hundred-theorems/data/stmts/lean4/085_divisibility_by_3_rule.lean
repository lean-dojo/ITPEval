/-
Copyright (c) 2020 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison, Shing Tak Lam, Mario Carneiro
-/
module

public import Mathlib.Data.List.Palindrome
public import Mathlib.Data.Nat.Digits.Lemmas

/-!
# Divisibility tests for natural numbers in terms of digits.

We prove some divisibility tests based on digits, in particular completing
Theorem #85 from https://www.cs.ru.nl/~freek/100/.

-/

public section

namespace Nat

variable {n : ℕ}

theorem modEq_three_digits_sum (n : ℕ) : n ≡ (digits 10 n).sum [MOD 3] :=
  modEq_digits_sum 3 10 (by simp) n

theorem modEq_nine_digits_sum (n : ℕ) : n ≡ (digits 10 n).sum [MOD 9] :=
  modEq_digits_sum 9 10 (by simp) n

theorem modEq_eleven_digits_sum (n : ℕ) :
    n ≡ ((digits 10 n).map fun n : ℕ => (n : ℤ)).alternatingSum [ZMOD 11] := by sorry
theorem dvd_iff_dvd_digits_sum (b b' : ℕ) (h : b' % b = 1) (n : ℕ) :
    b ∣ n ↔ b ∣ (digits b' n).sum := by sorry
theorem three_dvd_iff (n : ℕ) : 3 ∣ n ↔ 3 ∣ (digits 10 n).sum :=
  dvd_iff_dvd_digits_sum 3 10 (by simp) n

theorem nine_dvd_iff (n : ℕ) : 9 ∣ n ↔ 9 ∣ (digits 10 n).sum :=
  dvd_iff_dvd_digits_sum 9 10 (by simp) n

theorem dvd_iff_dvd_ofDigits (b b' : ℕ) (c : ℤ) (h : (b : ℤ) ∣ (b' : ℤ) - c) (n : ℕ) :
    b ∣ n ↔ (b : ℤ) ∣ ofDigits c (digits b' n) := by sorry
theorem eleven_dvd_iff :
    11 ∣ n ↔ (11 : ℤ) ∣ ((digits 10 n).map fun n : ℕ => (n : ℤ)).alternatingSum := by sorry
theorem eleven_dvd_of_palindrome (p : (digits 10 n).Palindrome) (h : Even (digits 10 n).length) :
    11 ∣ n := by sorry
end Nat
