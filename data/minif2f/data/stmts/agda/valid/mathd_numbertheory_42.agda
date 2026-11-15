-- Statement-only formalization of miniF2F valid problem mathd_numbertheory_42. This file
-- contains no proof.

module mathd-numbertheory-42 where

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

mathd-numbertheory-42 : Set
mathd-numbertheory-42 =
  (u v : Nat) →
  naturalMod (27 * u) 40 ≡ 17 →
  naturalMod (27 * v) 40 ≡ 17 →
  u < 40 →
  v < 80 →
  40 < v →
  u + v ≡ 62
