-- Statement-only formalization of miniF2F valid problem mathd_numbertheory_35. This file
-- contains no proof.

module mathd-numbertheory-35 where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; _+_; _*_)

infix 4 _∣_ _∈_ _∈ₛ_
infix 2 _↔_

data ⊥ : Set where

record _↔_ (A B : Set) : Set where
  constructor iff
  field
    forward  : A → B
    backward : B → A

record _∣_ (divisor dividend : Nat) : Set where
  constructor divides
  field
    quotient : Nat
    equation : divisor * quotient ≡ dividend

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

record FiniteSet (A : Set) : Set where
  constructor finite-set
  field
    elements     : List A
    noDuplicates : NoDuplicates elements

_∈ₛ_ : {A : Set} → A → FiniteSet A → Set
x ∈ₛ S = x ∈ FiniteSet.elements S

sumList : List Nat → Nat
sumList [] = zero
sumList (x ∷ xs) = x + sumList xs

sumFinite : FiniteSet Nat → Nat
sumFinite S = sumList (FiniteSet.elements S)

mathd-numbertheory-35 : Set
mathd-numbertheory-35 =
  (root : Nat) →
  root * root ≡ 196 →
  (S : FiniteSet Nat) →
  ((n : Nat) → (n ∈ₛ S) ↔ (n ∣ root)) →
  sumFinite S ≡ 24
