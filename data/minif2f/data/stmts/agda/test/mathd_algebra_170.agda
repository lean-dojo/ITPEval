-- Statement-only formalization of miniF2F test problem mathd_algebra_170. This file contains no
-- proof.

module mathd-algebra-170 where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Int using (Int; pos; negsuc)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _*_)

infix 4 _≤_ _∈_
infix 2 _↔_

data ⊥ : Set where

record _↔_ (A B : Set) : Set where
  field
    forward  : A → B
    backward : B → A

data _≤_ : Nat → Nat → Set where
  zero≤ : {n : Nat} → zero ≤ n
  suc≤suc : {m n : Nat} → m ≤ n → suc m ≤ suc n

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

naturalDistance : Nat → Nat → Nat
naturalDistance zero zero = zero
naturalDistance zero (suc n) = suc n
naturalDistance (suc m) zero = suc m
naturalDistance (suc m) (suc n) = naturalDistance m n

distanceFromTwo : Int → Nat
distanceFromTwo (pos n) = naturalDistance n 2
distanceFromTwo (negsuc n) = suc (suc (suc n))

WithinRadius : Int → Set
WithinRadius n = 10 * distanceFromTwo n ≤ 56

mathd-algebra-170 : Set
mathd-algebra-170 =
  (S : List Int) →
  NoDuplicates S →
  ((n : Int) → (n ∈ S) ↔ WithinRadius n) →
  length S ≡ 11
