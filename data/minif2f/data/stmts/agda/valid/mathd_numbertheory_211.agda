-- Statement-only formalization of miniF2F valid problem mathd_numbertheory_211. This file
-- contains no proof.

module mathd-numbertheory-211 where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using
  (Nat; zero; suc; _-_; _*_; mod-helper)

naturalMod : Nat → Nat → Nat
naturalMod numerator zero = zero
naturalMod numerator (suc denominator) =
  mod-helper zero denominator numerator denominator

natEqual : Nat → Nat → Bool
natEqual zero zero = true
natEqual zero (suc n) = false
natEqual (suc m) zero = false
natEqual (suc m) (suc n) = natEqual m n

qualifies : Nat → Bool
qualifies zero = false
qualifies (suc n) =
  natEqual (naturalMod (4 * suc n - 2) 6) zero

countQualifyingBelow : Nat → Nat
countQualifyingBelow zero = zero
countQualifyingBelow (suc bound) with qualifies bound
... | true = suc (countQualifyingBelow bound)
... | false = countQualifyingBelow bound

mathd-numbertheory-211 : Set
mathd-numbertheory-211 =
  countQualifyingBelow 60 ≡ 20
