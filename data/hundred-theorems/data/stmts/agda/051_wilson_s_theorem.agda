-- Statement-only formalization of Hundred Theorems artifact hundred-theorems__agda__051,
-- "Wilson's Theorem": for each natural number p other than 1, p is prime exactly when
-- p divides (p - 1)! + 1, equivalently (p - 1)! is congruent to -1 modulo p.
-- This file contains no proof.

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _-_; _*_)

infix 4 _≤_ _≠_ _∣_
infixr 3 _∨_
infix 2 _↔_

data ⊥ : Set where

_≠_ : {A : Set} → A → A → Set
x ≠ y = x ≡ y → ⊥

data _≤_ : Nat → Nat → Set where
  zero≤ : {n : Nat} → zero ≤ n
  suc≤suc : {m n : Nat} → m ≤ n → suc m ≤ suc n

record _∣_ (divisor dividend : Nat) : Set where
  field
    quotient : Nat
    division-equation : divisor * quotient ≡ dividend

data _∨_ (A B : Set) : Set where
  or-left : A → A ∨ B
  or-right : B → A ∨ B

record _↔_ (A B : Set) : Set where
  field
    forward : A → B
    backward : B → A

record Prime (n : Nat) : Set where
  field
    at-least-two : 2 ≤ n
    divisor-is-trivial :
      (d : Nat) →
      d ∣ n →
      d ≡ 1 ∨ d ≡ n

factorial : Nat → Nat
factorial zero = 1
factorial (suc n) = suc n * factorial n

CongruentToMinusOne : Nat → Nat → Set
CongruentToMinusOne value modulus =
  modulus ∣ (value + 1)

wilson-s-theorem : Set
wilson-s-theorem =
  (p : Nat) →
  p ≠ 1 →
  (Prime p ↔ CongruentToMinusOne (factorial (p - 1)) p)
