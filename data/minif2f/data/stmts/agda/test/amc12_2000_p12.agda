-- Statement-only formalization of miniF2F test problem amc12_2000_p12. This file contains no
-- proof.

module amc12-2000-p12 where

open import Agda.Builtin.Bool using (true)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat; suc; _+_; _*_; _<_)

infix 4 _≤_

_≤_ : Nat → Nat → Set
m ≤ n = (m < suc n) ≡ true

amc12-2000-p12 : Set
amc12-2000-p12 =
  (a m c : Nat) →
  a + m + c ≡ 12 →
  a * m * c + a * m + m * c + a * c ≤ 112
