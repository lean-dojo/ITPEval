-- Statement-only formalization of Hundred Theorems corpus artifact
-- hundred-theorems__agda__098, "Bertrand's Postulate": every natural number at least two
-- has a prime number strictly between it and its double. This file contains no proof.

module BertrandsPostulate where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _*_)

infix 4 _≤_ _<_ _∣_
infixr 5 _×_
infixr 3 _∨_

data _≤_ : Nat → Nat → Set where
  zero≤ : {n : Nat} → zero ≤ n
  suc≤suc : {m n : Nat} → m ≤ n → suc m ≤ suc n

_<_ : Nat → Nat → Set
m < n = suc m ≤ n

record _×_ (A B : Set) : Set where
  field
    left : A
    right : B

record _∣_ (divisor dividend : Nat) : Set where
  field
    quotient : Nat
    equation : dividend ≡ divisor * quotient

data _∨_ (A B : Set) : Set where
  left : A → A ∨ B
  right : B → A ∨ B

record Prime (n : Nat) : Set where
  field
    at-least-two : 2 ≤ n
    only-trivial-divisors : (d : Nat) → d ∣ n → (d ≡ 1) ∨ (d ≡ n)

record Exists (A : Set) (P : A → Set) : Set where
  field
    witness : A
    satisfies : P witness

bertrands-postulate : Set
bertrands-postulate =
  (n : Nat) →
  2 ≤ n →
  Exists Nat (λ p → Prime p × ((n < p) × (p < 2 * n)))
