-- Statement-only formalization of miniF2F test problem mathd_numbertheory_559. This file
-- contains no proof.

module mathd-numbertheory-559 where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat; zero; suc; mod-helper)

infix 4 _≤_

data _≤_ : Nat → Nat → Set where
  zero≤ : {n : Nat} → zero ≤ n
  suc≤suc : {m n : Nat} → m ≤ n → suc m ≤ suc n

naturalMod : Nat → Nat → Nat
naturalMod numerator zero = zero
naturalMod numerator (suc denominator) =
  mod-helper zero denominator numerator denominator

mathd-numbertheory-559 : Set
mathd-numbertheory-559 =
  (x y : Nat) →
  naturalMod x 3 ≡ 2 →
  naturalMod y 5 ≡ 4 →
  naturalMod x 10 ≡ naturalMod y 10 →
  14 ≤ x
