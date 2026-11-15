-- Statement-only formalization of miniF2F valid problem mathd_numbertheory_24. This file
-- contains no proof.

module mathd-numbertheory-24 where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using
  (Nat; zero; suc; _+_; _*_; mod-helper)

infixr 8 _^_

_^_ : Nat → Nat → Nat
base ^ zero = 1
base ^ (suc exponent) = base * (base ^ exponent)

sumFromOne : Nat → (Nat → Nat) → Nat
sumFromOne zero term = zero
sumFromOne (suc n) term = sumFromOne n term + term (suc n)

naturalMod : Nat → Nat → Nat
naturalMod numerator zero = zero
naturalMod numerator (suc denominator) =
  mod-helper zero denominator numerator denominator

mathd-numbertheory-24 : Set
mathd-numbertheory-24 =
  naturalMod (sumFromOne 9 (λ k → 11 ^ k)) 100 ≡ 59
