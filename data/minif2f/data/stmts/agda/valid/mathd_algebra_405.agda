-- Statement-only formalization of miniF2F valid problem mathd_algebra_405. This file contains
-- no proof.

module mathd-algebra-405 where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)

infix 4 _<_ _∈_ _∈ₛ_
infixr 3 _∧_
infixr 2 _∨_
infix 1 _↔_

data ⊥ : Set where

data _<_ : Nat → Nat → Set where
  zero-less-successor :
    {n : Nat} →
    zero < suc n
  successor-less-successor :
    {m n : Nat} →
    m < n →
    suc m < suc n

data _∨_ (A B : Set) : Set where
  left  : A → A ∨ B
  right : B → A ∨ B

record _∧_ (A B : Set) : Set where
  field
    first  : A
    second : B

record _↔_ (A B : Set) : Set where
  field
    forward  : A → B
    backward : B → A

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
  field
    elements     : List A
    noDuplicates : NoDuplicates elements

_∈ₛ_ : {A : Set} → A → FiniteSet A → Set
x ∈ₛ S = x ∈ FiniteSet.elements S

length : {A : Set} → List A → Nat
length [] = zero
length (_ ∷ xs) = suc (length xs)

cardinality : {A : Set} → FiniteSet A → Nat
cardinality S = length (FiniteSet.elements S)

SolutionCondition : Nat → Set
SolutionCondition x =
  zero < x ∧ x * x + 4 * x + 4 < 20

PointwiseForm : Set
PointwiseForm =
  (x : Nat) →
  zero < x →
  x * x + 4 * x + 4 < 20 →
  x ≡ 1 ∨ x ≡ 2

FiniteSetForm : Set
FiniteSetForm =
  (S : FiniteSet Nat) →
  ((x : Nat) →
    (x ∈ₛ S) ↔ SolutionCondition x) →
  cardinality S ≡ 2

mathd-algebra-405 : Set
mathd-algebra-405 = PointwiseForm ∧ FiniteSetForm
