-- Statement-only formalization of "All Primes (1 mod 4) Equal the Sum of Two Squares" from
-- Hundred Theorems item 020. This file contains no proof.

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)

infix 4 _≤_ _∣_
infixr 3 _∨_

data _≤_ : Nat → Nat → Set where
  z≤n : {n : Nat} → zero ≤ n
  s≤s : {m n : Nat} → m ≤ n → suc m ≤ suc n

record _∣_ (d n : Nat) : Set where
  field
    quotient : Nat
    division-equation : n ≡ d * quotient

data _∨_ (A B : Set) : Set where
  or-left : A → A ∨ B
  or-right : B → A ∨ B

record Prime (n : Nat) : Set where
  field
    at-least-two : 2 ≤ n
    divisor-is-trivial : (d : Nat) → d ∣ n → d ≡ 1 ∨ d ≡ n

record Exists (A : Set) (P : A → Set) : Set where
  constructor witness
  field
    value : A
    property : P value

square : Nat → Nat
square n = n * n

all-primes-one-mod-four-are-sums-of-two-squares : Set
all-primes-one-mod-four-are-sums-of-two-squares =
  (p k : Nat) →
  Prime p →
  p ≡ 4 * k + 1 →
  Exists Nat (λ x →
    Exists Nat (λ y →
      p ≡ square x + square y))
