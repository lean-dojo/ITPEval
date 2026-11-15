-- Statement-only formalization of miniF2F test problem amc12_2001_p21. This file contains no
-- proof.

module amc12-2001-p21 where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Int using (Int; pos; negsuc)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)

factorial : Nat → Nat
factorial zero = 1
factorial (suc n) = suc n * factorial n

difference : Nat → Nat → Int
difference zero zero = pos zero
difference (suc m) zero = pos (suc m)
difference zero (suc n) = negsuc n
difference (suc m) (suc n) = difference m n

amc12-2001-p21 : Set
amc12-2001-p21 =
  (a b c d : Nat) →
  a * b * c * d ≡ factorial 8 →
  a * b + a + b ≡ 524 →
  b * c + b + c ≡ 146 →
  c * d + c + d ≡ 104 →
  difference a d ≡ pos 10
