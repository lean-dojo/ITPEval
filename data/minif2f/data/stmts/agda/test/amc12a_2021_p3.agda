-- Statement-only formalization of miniF2F test problem amc12a_2021_p3. This file contains no
-- proof.

module amc12a-2021-p3 where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Int using (Int; pos; negsuc)
open import Agda.Builtin.Nat using
  (Nat; zero; suc; _+_; _*_; div-helper)

record Divides (d n : Nat) : Set where
  field
    quotient : Nat
    product  : d * quotient ≡ n

naturalDiv : Nat → Nat → Nat
naturalDiv numerator zero = zero
naturalDiv numerator (suc denominator) =
  div-helper zero denominator numerator denominator

difference : Nat → Nat → Int
difference zero zero = pos zero
difference (suc m) zero = pos (suc m)
difference zero (suc n) = negsuc n
difference (suc m) (suc n) = difference m n

amc12a-2021-p3 : Set
amc12a-2021-p3 =
  (x y : Nat) →
  x + y ≡ 17402 →
  Divides 10 x →
  naturalDiv x 10 ≡ y →
  difference x y ≡ pos 14238
