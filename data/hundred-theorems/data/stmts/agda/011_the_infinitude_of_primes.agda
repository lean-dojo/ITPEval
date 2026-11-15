-- Statement-only formalization of Hundred Theorems artifact hundred-theorems__agda__011,
-- "The Infinitude of Primes": every natural-number bound is at most some prime number.
-- This file contains no proof.

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _*_)

infix 4 _≤_ _∣_
infixr 5 _×_
infixr 3 _∨_

data _≤_ : Nat → Nat → Set where
  zero≤ : {n : Nat} → zero ≤ n
  suc≤suc : {m n : Nat} → m ≤ n → suc m ≤ suc n

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
    divisor-is-trivial :
      (d : Nat) →
      d ∣ n →
      d ≡ 1 ∨ d ≡ n

record Exists (A : Set) (P : A → Set) : Set where
  field
    value : A
    property : P value

the-infinitude-of-primes : Set
the-infinitude-of-primes =
  (n : Nat) →
  Exists Nat (λ p → Prime p × (n ≤ p))
