-- Statement-only formalization of Hundred Theorems corpus artifact
-- hundred-theorems__agda__070, "The Perfect Number Theorem": the Euclid-Euler
-- characterization of even perfect natural numbers as powers of two times Mersenne primes.
-- This file contains no proof.

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _-_; _*_)

infix 4 _≤_ _∣_ _∈_
infixr 5 _∷_
infixr 3 _∨_ _∧_
infix 2 _↔_
infixr 8 _^_

data _≤_ : Nat → Nat → Set where
  zero≤ : {n : Nat} → zero ≤ n
  suc≤suc : {m n : Nat} → m ≤ n → suc m ≤ suc n

record _∣_ (divisor dividend : Nat) : Set where
  field
    quotient : Nat
    equation : divisor * quotient ≡ dividend

data _∨_ (A B : Set) : Set where
  left : A → A ∨ B
  right : B → A ∨ B

record _∧_ (A B : Set) : Set where
  constructor conjunction
  field
    first : A
    second : B

record _↔_ (A B : Set) : Set where
  field
    forward : A → B
    backward : B → A

record Exists (A : Set) (P : A → Set) : Set where
  constructor witness
  field
    value : A
    property : P value

data ⊥ : Set where

data List (A : Set) : Set where
  [] : List A
  _∷_ : A → List A → List A

data _∈_ {A : Set} (x : A) : List A → Set where
  here : {xs : List A} → x ∈ (x ∷ xs)
  there : {y : A} {xs : List A} → x ∈ xs → x ∈ (y ∷ xs)

data NoDuplicates {A : Set} : List A → Set where
  no-duplicates-empty : NoDuplicates []
  no-duplicates-cons :
    {x : A} {xs : List A} →
    (x ∈ xs → ⊥) →
    NoDuplicates xs →
    NoDuplicates (x ∷ xs)

sum : List Nat → Nat
sum [] = zero
sum (x ∷ xs) = x + sum xs

record IsDivisorSum (n total : Nat) : Set where
  field
    divisors : List Nat
    exact-divisors :
      (d : Nat) → (d ∈ divisors) ↔ (d ∣ n)
    no-duplicate-divisors : NoDuplicates divisors
    sum-equation : sum divisors ≡ total

record Prime (n : Nat) : Set where
  field
    at-least-two : 2 ≤ n
    divisor-is-trivial :
      (d : Nat) →
      d ∣ n →
      d ≡ 1 ∨ d ≡ n

_^_ : Nat → Nat → Nat
base ^ zero = 1
base ^ suc exponent = base * (base ^ exponent)

Even : Nat → Set
Even n = Exists Nat (λ half → 2 * half ≡ n)

Perfect : Nat → Set
Perfect n = 1 ≤ n ∧ IsDivisorSum n (2 * n)

mersenne : Nat → Nat
mersenne k = 2 ^ suc k - 1

perfect-number-theorem : Set
perfect-number-theorem =
  (n : Nat) →
  (Even n ∧ Perfect n) ↔
  Exists Nat (λ k →
    Prime (mersenne k) ∧
    n ≡ (2 ^ k) * mersenne k)
