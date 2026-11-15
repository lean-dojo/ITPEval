-- Statement-only formalization of miniF2F valid problem mathd_numbertheory_13:
-- positive natural solutions of 14 * n modulo 100 and their average. This file
-- contains no proof.

module mathd-numbertheory-13 where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using
  (Nat; zero; suc; _+_; _*_; div-helper; mod-helper)

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

naturalDiv : Nat → Nat → Nat
naturalDiv numerator zero = zero
naturalDiv numerator (suc denominator) =
  div-helper zero denominator numerator denominator

mathd-numbertheory-13 : Set
mathd-numbertheory-13 =
  (u v : Nat) →
  zero < u →
  zero < v →
  naturalMod (14 * u) 100 ≡ 46 →
  naturalMod (14 * v) 100 ≡ 46 →
  u < 50 →
  50 < v →
  v < 100 →
  naturalDiv (u + v) 2 ≡ 64
