-- Statement-only formalization of miniF2F valid problem mathd_numbertheory_301:
-- for every positive natural j, 3 * (7 * j + 3) has remainder 2 modulo 7.
-- This file contains no proof.

module mathd-numbertheory-301 where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using
  (Nat; zero; suc; _+_; _*_; mod-helper)

infix 4 _≤_ _<_

data _≤_ : Nat → Nat → Set where
  zero≤ : {n : Nat} → zero ≤ n
  suc≤suc : {m n : Nat} → m ≤ n → suc m ≤ suc n

_<_ : Nat → Nat → Set
m < n = suc m ≤ n

naturalMod : Nat → Nat → Nat
naturalMod numerator zero = zero
naturalMod numerator (suc denominator) =
  mod-helper zero denominator numerator denominator

mathd-numbertheory-301 : Set
mathd-numbertheory-301 =
  (j : Nat) →
  zero < j →
  naturalMod (3 * (7 * j + 3)) 7 ≡ 2
