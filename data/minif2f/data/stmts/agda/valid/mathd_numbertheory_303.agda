-- Statement-only formalization of miniF2F valid problem mathd_numbertheory_303. This file
-- contains no proof.

module mathd-numbertheory-303 where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using
  (Nat; zero; suc; _+_; mod-helper)

infix 4 _≤_ _∈_
infixr 4 _∧_
infix 2 _↔_

data ⊥ : Set where

data _≤_ : Nat → Nat → Set where
  zero≤ : {n : Nat} → zero ≤ n
  suc≤suc : {m n : Nat} → m ≤ n → suc m ≤ suc n

record _∧_ (A B : Set) : Set where
  field
    first  : A
    second : B

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

naturalMod : Nat → Nat → Nat
naturalMod numerator zero = numerator
naturalMod numerator (suc denominator) =
  mod-helper zero denominator numerator denominator

sum : List Nat → Nat
sum [] = zero
sum (x ∷ xs) = x + sum xs

mathd-numbertheory-303 : Set
mathd-numbertheory-303 =
  (S : List Nat) →
  ((n : Nat) →
    (n ∈ S) ↔
    ((2 ≤ n) ∧
      ((naturalMod 171 n ≡ naturalMod 80 n) ∧
       (naturalMod 468 n ≡ naturalMod 13 n)))) →
  NoDuplicates S →
  sum S ≡ 111
