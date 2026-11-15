-- Statement-only formalization of miniF2F valid problem mathd_numbertheory_110. This file
-- contains no proof.

module mathd-numbertheory-110 where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using
  (Nat; zero; suc; _+_; _-_; _*_; mod-helper)

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

mathd-numbertheory-110 : Set
mathd-numbertheory-110 =
  (a b : Nat) →
  zero < a →
  zero < b →
  b ≤ a →
  naturalMod (a + b) 10 ≡ 2 →
  naturalMod (2 * a + b) 10 ≡ 1 →
  naturalMod (a - b) 10 ≡ 6
