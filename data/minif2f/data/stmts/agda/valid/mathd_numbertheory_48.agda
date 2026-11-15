-- Statement-only formalization of miniF2F valid problem mathd_numbertheory_48. This file
-- contains no proof.

module mathd-numbertheory-48 where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)

infix 4 _≤_ _<_
infixr 8 _^_

data _≤_ : Nat → Nat → Set where
  zero≤ : {n : Nat} → zero ≤ n
  suc≤suc : {m n : Nat} → m ≤ n → suc m ≤ suc n

_<_ : Nat → Nat → Set
m < n = suc m ≤ n

_^_ : Nat → Nat → Nat
base ^ zero = 1
base ^ (suc exponent) = base * (base ^ exponent)

mathd-numbertheory-48 : Set
mathd-numbertheory-48 =
  (b : Nat) →
  zero < b →
  3 * b ^ 2 + 2 * b + 1 ≡ 57 →
  b ≡ 4
