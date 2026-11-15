-- Statement-only formalization of miniF2F test problem amc12a_2020_p7. This file contains no
-- proof.

module amc12a-2020-p7 where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Int using (Int; pos; negsuc)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)

power : Nat → Nat → Nat
power x zero = 1
power x (suc n) = x * power x n

sumSquares : Nat → (Nat → Nat) → Nat
sumSquares zero a = zero
sumSquares (suc n) a = sumSquares n a + a n * a n

difference : Nat → Nat → Int
difference zero zero = pos zero
difference (suc m) zero = pos (suc m)
difference zero (suc n) = negsuc n
difference (suc m) (suc n) = difference m n

amc12a-2020-p7 : Set
amc12a-2020-p7 =
  (a : Nat → Nat) →
  power (a 0) 3 ≡ 1 →
  power (a 1) 3 ≡ 8 →
  power (a 2) 3 ≡ 27 →
  power (a 3) 3 ≡ 64 →
  power (a 4) 3 ≡ 125 →
  power (a 5) 3 ≡ 216 →
  power (a 6) 3 ≡ 343 →
  difference
    (6 * sumSquares 7 a)
    (2 * sumSquares 6 a)
  ≡ pos 658
