-- Statement-only formalization of miniF2F test problem mathd_numbertheory_447. This file
-- contains no proof.

module mathd-numbertheory-447 where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using
  (Nat; zero; suc; _+_; mod-helper)

naturalMod : Nat → Nat → Nat
naturalMod numerator zero = zero
naturalMod numerator (suc denominator) =
  mod-helper zero denominator numerator denominator

sumRemaindersOfMultiplesOfThreeUpTo : Nat → Nat
sumRemaindersOfMultiplesOfThreeUpTo zero = zero
sumRemaindersOfMultiplesOfThreeUpTo (suc bound)
  with naturalMod (suc bound) 3
... | zero =
  naturalMod (suc bound) 10 +
  sumRemaindersOfMultiplesOfThreeUpTo bound
... | suc _ =
  sumRemaindersOfMultiplesOfThreeUpTo bound

mathd-numbertheory-447 : Set
mathd-numbertheory-447 =
  sumRemaindersOfMultiplesOfThreeUpTo 49 ≡ 78
