-- Statement-only formalization of miniF2F test problem mathd_numbertheory_5:
-- a natural number at least 10 that is both a perfect square and a perfect cube
-- is at least 64. This file contains no proof.

module mathd-numbertheory-5 where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _*_)

infix 4 _≤_
infixr 8 _^_

data _≤_ : Nat → Nat → Set where
  zero≤ : {n : Nat} → zero ≤ n
  suc≤suc : {m n : Nat} → m ≤ n → suc m ≤ suc n

_^_ : Nat → Nat → Nat
base ^ zero = 1
base ^ (suc exponent) = base * (base ^ exponent)

record Exists (A : Set) (P : A → Set) : Set where
  constructor witness
  field
    value : A
    property : P value

mathd-numbertheory-5 : Set
mathd-numbertheory-5 =
  (n : Nat) →
  10 ≤ n →
  Exists Nat (λ x → x ^ 2 ≡ n) →
  Exists Nat (λ t → t ^ 3 ≡ n) →
  64 ≤ n
