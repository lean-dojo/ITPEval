-- Statement-only formalization of miniF2F valid problem mathd_numbertheory_709. This file
-- contains no proof.

module mathd-numbertheory-709 where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using
  (Nat; zero; suc; _*_; mod-helper)

infix 4 _≤_ _<_

data _≤_ : Nat → Nat → Set where
  zero≤ : {n : Nat} → zero ≤ n
  suc≤suc : {m n : Nat} → m ≤ n → suc m ≤ suc n

_<_ : Nat → Nat → Set
m < n = suc m ≤ n

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

mathd-numbertheory-709 : Set
mathd-numbertheory-709 =
  (n : Nat) →
  zero < n →
  divisorCount (2 * n) ≡ 28 →
  divisorCount (3 * n) ≡ 30 →
  divisorCount (6 * n) ≡ 35
