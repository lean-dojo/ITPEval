-- Statement-only formalization of miniF2F valid problem mathd_numbertheory_232:
-- the inverse modulo 31 of the sum of the inverses of 3 and 5 is 29. This file
-- contains no proof.

module mathd-numbertheory-232 where

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

mathd-numbertheory-232 : Set
mathd-numbertheory-232 =
  (x y z : Nat) →
  x < 31 →
  y < 31 →
  z < 31 →
  naturalMod (x * 3) 31 ≡ 1 →
  naturalMod (y * 5) 31 ≡ 1 →
  naturalMod (z * (x + y)) 31 ≡ 1 →
  z ≡ 29
