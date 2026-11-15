-- Statement-only formalization of miniF2F valid problem mathd_numbertheory_221:
-- exactly 11 positive natural numbers below 1000 have exactly three positive divisors.
-- This file contains no proof.

module mathd-numbertheory-221 where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat; zero; suc; mod-helper)

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

hasThreeDivisors : Nat → Bool
hasThreeDivisors number = natEqual (divisorCount number) 3

countThreeDivisorsBelow : Nat → Nat
countThreeDivisorsBelow zero = zero
countThreeDivisorsBelow (suc bound) with hasThreeDivisors bound
... | true = suc (countThreeDivisorsBelow bound)
... | false = countThreeDivisorsBelow bound

mathd-numbertheory-221 : Set
mathd-numbertheory-221 =
  countThreeDivisorsBelow 1000 ≡ 11
