-- Statement-only formalization of miniF2F test problem amc12a_2020_p4: counting
-- four-digit natural numbers whose decimal digits are even and which are divisible by 5.
-- This file contains no proof.

module amc12a-2020-p4 where

open import Agda.Builtin.Bool using (true)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_; _<_)

infix 4 _≤_ _∈_
infixr 3 _∧_
infix 2 _↔_

data ⊥ : Set where

_≤_ : Nat → Nat → Set
m ≤ n = (m < suc n) ≡ true

record _∧_ (A B : Set) : Set where
  constructor conjunction
  field
    left  : A
    right : B

record _↔_ (A B : Set) : Set where
  field
    forward  : A → B
    backward : B → A

record Exists (A : Set) (P : A → Set) : Set where
  constructor witness
  field
    value    : A
    property : P value

data _∈_ {A : Set} (x : A) : List A → Set where
  here  : {xs : List A} → x ∈ (x ∷ xs)
  there : {y : A} {xs : List A} → x ∈ xs → x ∈ (y ∷ xs)

data NoDuplicates {A : Set} : List A → Set where
  no-duplicates-empty :
    NoDuplicates []
  no-duplicates-cons :
    {x : A} {xs : List A} →
    (x ∈ xs → ⊥) →
    NoDuplicates xs →
    NoDuplicates (x ∷ xs)

length : {A : Set} → List A → Nat
length [] = zero
length (_ ∷ xs) = suc (length xs)

Even : Nat → Set
Even n = Exists Nat (λ k → 2 * k ≡ n)

record Divides (d n : Nat) : Set where
  field
    quotient : Nat
    product  : d * quotient ≡ n

FourDigitEvenMultipleOfFive : Nat → Set
FourDigitEvenMultipleOfFive n =
  Exists Nat λ a →
  Exists Nat λ b →
  Exists Nat λ c →
  Exists Nat λ d →
    (1 ≤ a) ∧
    (a ≤ 9) ∧
    Even a ∧
    (b ≤ 9) ∧
    Even b ∧
    (c ≤ 9) ∧
    Even c ∧
    (d ≤ 9) ∧
    Even d ∧
    (n ≡ 1000 * a + 100 * b + 10 * c + d) ∧
    Divides 5 n

amc12a-2020-p4 : Set
amc12a-2020-p4 =
  (solutions : List Nat) →
  ((n : Nat) →
    (n ∈ solutions) ↔ FourDigitEvenMultipleOfFive n) →
  NoDuplicates solutions →
  length solutions ≡ 100
