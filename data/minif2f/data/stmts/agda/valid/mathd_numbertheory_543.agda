-- Statement-only formalization of miniF2F valid problem mathd_numbertheory_543. This file
-- contains no proof.

module mathd-numbertheory-543 where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using
  (Nat; zero; suc; _-_; _*_; mod-helper)

infixr 8 _^_

_^_ : Nat → Nat → Nat
base ^ zero = 1
base ^ (suc exponent) = base * (base ^ exponent)

natEqual : Nat → Nat → Bool
natEqual zero zero = true
natEqual zero (suc n) = false
natEqual (suc m) zero = false
natEqual (suc m) (suc n) = natEqual m n

naturalMod : Nat → Nat → Nat
naturalMod numerator zero = zero
naturalMod numerator (suc denominator) =
  mod-helper zero denominator numerator denominator

divisorCountUpTo : Nat → Nat → Nat
divisorCountUpTo number zero = zero
divisorCountUpTo number (suc bound)
  with natEqual (naturalMod number (suc bound)) zero
... | true = suc (divisorCountUpTo number bound)
... | false = divisorCountUpTo number bound

divisorCount : Nat → Nat
divisorCount number = divisorCountUpTo number number

mathd-numbertheory-543 : Set
mathd-numbertheory-543 =
  divisorCount (30 ^ 4) - 2 ≡ 123
