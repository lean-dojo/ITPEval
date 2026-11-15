-- Statement-only formalization of miniF2F test problem mathd_numbertheory_237. This file
-- contains no proof.

module mathd-numbertheory-237 where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using
  (Nat; zero; suc; _+_; mod-helper)

sumRange : Nat → Nat
sumRange zero = zero
sumRange (suc n) = sumRange n + n

naturalMod : Nat → Nat → Nat
naturalMod numerator zero = zero
naturalMod numerator (suc denominator) =
  mod-helper zero denominator numerator denominator

mathd-numbertheory-237 : Set
mathd-numbertheory-237 =
  naturalMod (sumRange 101) 6 ≡ 4
