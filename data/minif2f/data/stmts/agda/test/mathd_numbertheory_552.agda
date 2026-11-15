-- Statement-only formalization of miniF2F test problem mathd_numbertheory_552:
-- the distinct gcd values of 12x + 7 and 5x + 2 over positive naturals sum to 12.
-- This file contains no proof.

module mathd-numbertheory-552 where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)

infix 4 _∈_ _∣_
infixr 3 _∧_
infix 2 _↔_

data ⊥ : Set where

data Positive : Nat → Set where
  positive : {n : Nat} → Positive (suc n)

record _∧_ (A B : Set) : Set where
  constructor conjunction
  field
    left  : A
    right : B

record _↔_ (A B : Set) : Set where
  constructor iff
  field
    forward  : A → B
    backward : B → A

record Exists (A : Set) (P : A → Set) : Set where
  constructor witness
  field
    value    : A
    property : P value

data _∈_ {A : Set} (x : A) : List A → Set where
  here :
    {y : A} {ys : List A} →
    x ≡ y →
    x ∈ (y ∷ ys)
  there :
    {y : A} {ys : List A} →
    x ∈ ys →
    x ∈ (y ∷ ys)

data NoDuplicates {A : Set} : List A → Set where
  no-duplicates-empty :
    NoDuplicates []
  no-duplicates-cons :
    {x : A} {xs : List A} →
    (x ∈ xs → ⊥) →
    NoDuplicates xs →
    NoDuplicates (x ∷ xs)

record _∣_ (divisor dividend : Nat) : Set where
  field
    quotient : Nat
    equation : divisor * quotient ≡ dividend

record IsGCD (a b g : Nat) : Set where
  field
    gcd-divides-left : g ∣ a
    gcd-divides-right : g ∣ b
    greatest-common-divisor :
      (d : Nat) →
      d ∣ a →
      d ∣ b →
      d ∣ g

record FinitePositiveRange (h : Nat → Nat) : Set where
  constructor finite-positive-range
  field
    elements : List Nat
    noDuplicates : NoDuplicates elements
    exact-membership :
      (y : Nat) →
      (y ∈ elements) ↔
      Exists Nat (λ x → Positive x ∧ (h x ≡ y))

sumList : List Nat → Nat
sumList [] = zero
sumList (x ∷ xs) = x + sumList xs

mathd-numbertheory-552 : Set
mathd-numbertheory-552 =
  (f g h : Nat → Nat) →
  ((x : Nat) → Positive x → f x ≡ 12 * x + 7) →
  ((x : Nat) → Positive x → g x ≡ 5 * x + 2) →
  ((x : Nat) → Positive x → IsGCD (f x) (g x) (h x)) →
  (range : FinitePositiveRange h) →
  sumList (FinitePositiveRange.elements range) ≡ 12
