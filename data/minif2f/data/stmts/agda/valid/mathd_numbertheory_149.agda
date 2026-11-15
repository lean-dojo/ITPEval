-- Statement-only formalization of miniF2F valid problem mathd_numbertheory_149:
-- the natural numbers below 50 with remainders 5 modulo 8 and 3 modulo 6
-- have sum 66. This file contains no proof.

module mathd-numbertheory-149 where

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; mod-helper)

naturalMod : Nat → Nat → Nat
naturalMod numerator zero = zero
naturalMod numerator (suc denominator) =
  mod-helper zero denominator numerator denominator

natEqual : Nat → Nat → Bool
natEqual zero zero = true
natEqual zero (suc n) = false
natEqual (suc m) zero = false
natEqual (suc m) (suc n) = natEqual m n

both : Bool → Bool → Bool
both true value = value
both false value = false

qualifies : Nat → Bool
qualifies n =
  both
    (natEqual (naturalMod n 8) 5)
    (natEqual (naturalMod n 6) 3)

selectedValue : Nat → Nat
selectedValue n with qualifies n
... | true = n
... | false = zero

filteredSumBelow : Nat → Nat
filteredSumBelow zero = zero
filteredSumBelow (suc bound) =
  filteredSumBelow bound + selectedValue bound

mathd-numbertheory-149 : Set
mathd-numbertheory-149 =
  filteredSumBelow 50 ≡ 66
