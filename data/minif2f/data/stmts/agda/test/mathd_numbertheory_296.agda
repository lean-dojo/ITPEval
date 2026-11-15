-- Statement-only formalization of miniF2F test problem mathd_numbertheory_296. This file
-- contains no proof.

module mathd-numbertheory-296 where

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

mathd-numbertheory-296 : Set
mathd-numbertheory-296 =
  (n : Nat) →
  2 ≤ n →
  Exists Nat (λ x → x ^ 3 ≡ n) →
  Exists Nat (λ t → t ^ 4 ≡ n) →
  4096 ≤ n
