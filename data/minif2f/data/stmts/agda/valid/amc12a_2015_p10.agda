-- Statement-only formalization of miniF2F valid problem amc12a_2015_p10:
-- the Diophantine equation x + y + xy = 80 with 0 < y < x forces x = 26.
-- This file contains no proof.

module amc12a-2015-p10 where

open import Agda.Builtin.Bool using (true)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat; zero; _+_; _*_; _<_)

NatLess : Nat → Nat → Set
NatLess m n = (m < n) ≡ true

amc12a-2015-p10 : Set
amc12a-2015-p10 =
  (x y : Nat) →
  NatLess zero y →
  NatLess y x →
  x + y + x * y ≡ 80 →
  x ≡ 26
