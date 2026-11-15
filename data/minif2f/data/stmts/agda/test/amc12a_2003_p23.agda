-- Statement-only formalization of miniF2F test problem amc12a_2003_p23: counting the positive
-- natural numbers whose squares divide the product 1! * ... * 9!. This file contains no proof.

module amc12a-2003-p23 where

open import Agda.Builtin.Bool using (true)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _*_; _<_)

infix 4 _≠_ _∈_
infixr 4 _∧_
infix 2 _↔_

data ⊥ : Set where

_≠_ : {A : Set} → A → A → Set
x ≠ y = x ≡ y → ⊥

record _∧_ (A B : Set) : Set where
  constructor conjunction
  field
    left  : A
    right : B

record _↔_ (A B : Set) : Set where
  field
    forward  : A → B
    backward : B → A

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

record Divides (d n : Nat) : Set where
  field
    quotient : Nat
    product  : d * quotient ≡ n

Positive : Nat → Set
Positive n = (zero < n) ≡ true

factorial : Nat → Nat
factorial zero = 1
factorial (suc n) = suc n * factorial n

factorialProduct : Nat → Nat
factorialProduct zero = 1
factorialProduct (suc n) =
  factorial (suc n) * factorialProduct n

Solution : Nat → Set
Solution k =
  Positive k ∧ Divides (k * k) (factorialProduct 9)

amc12a-2003-p23 : Set
amc12a-2003-p23 =
  (solutions : List Nat) →
  ((k : Nat) → (k ∈ solutions) ↔ Solution k) →
  NoDuplicates solutions →
  length solutions ≡ 672
