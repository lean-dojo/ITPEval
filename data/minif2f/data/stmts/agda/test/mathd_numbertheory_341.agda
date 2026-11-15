-- Statement-only formalization of miniF2F test problem mathd_numbertheory_341. This file
-- contains no proof.

module mathd-numbertheory-341 where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using
  (Nat; zero; suc; _+_; _*_; mod-helper)

infix 4 _≤_
infixr 8 _^_

data _≤_ : Nat → Nat → Set where
  zero≤ : {n : Nat} → zero ≤ n
  suc≤suc : {m n : Nat} → m ≤ n → suc m ≤ suc n

_^_ : Nat → Nat → Nat
base ^ zero = 1
base ^ (suc exponent) = base * (base ^ exponent)

naturalMod : Nat → Nat → Nat
naturalMod numerator zero = zero
naturalMod numerator (suc denominator) =
  mod-helper zero denominator numerator denominator

mathd-numbertheory-341 : Set
mathd-numbertheory-341 =
  (a b c : Nat) →
  a ≤ 9 →
  b ≤ 9 →
  c ≤ 9 →
  naturalMod (5 ^ 100) 1000 ≡ 100 * a + 10 * b + c →
  a + b + c ≡ 13
