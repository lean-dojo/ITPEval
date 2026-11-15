-- Statement-only formalization of miniF2F valid problem mathd_numbertheory_403: the sum
-- of the positive proper divisors of 198 is 270. This file contains no proof.

module mathd-numbertheory-403 where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using
  (Nat; zero; suc; _+_; mod-helper)

natEqual : Nat → Nat → Bool
natEqual zero zero = true
natEqual zero (suc n) = false
natEqual (suc m) zero = false
natEqual (suc m) (suc n) = natEqual m n

naturalMod : Nat → Nat → Nat
naturalMod numerator zero = zero
naturalMod numerator (suc denominator) =
  mod-helper zero denominator numerator denominator

sumDivisorsUpTo : Nat → Nat → Nat
sumDivisorsUpTo number zero = zero
sumDivisorsUpTo number (suc bound)
  with natEqual (naturalMod number (suc bound)) zero
... | true = suc bound + sumDivisorsUpTo number bound
... | false = sumDivisorsUpTo number bound

sumProperDivisors : Nat → Nat
sumProperDivisors zero = zero
sumProperDivisors (suc n) = sumDivisorsUpTo (suc n) n

mathd-numbertheory-403 : Set
mathd-numbertheory-403 = sumProperDivisors 198 ≡ 270
