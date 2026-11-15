-- Statement-only formalization of miniF2F valid problem mathd_numbertheory_155:
-- counting three-digit natural numbers congruent to 7 modulo 19. This file contains no proof.

module mathd-numbertheory-155 where

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

countResidueFrom : Nat → Nat → Nat → Nat → Nat
countResidueFrom modulus residue start zero = zero
countResidueFrom modulus residue start (suc length)
  with natEqual (naturalMod start modulus) residue
... | true =
  suc (countResidueFrom modulus residue (suc start) length)
... | false =
  countResidueFrom modulus residue (suc start) length

mathd-numbertheory-155 : Set
mathd-numbertheory-155 =
  countResidueFrom 19 7 100 900 ≡ 48
