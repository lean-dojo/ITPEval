-- Statement-only formalization of VERINA corpus artifact verina_basic_14,
-- catalog title "containsZ": a deterministic string traversal returns whether
-- the input contains the lowercase or uppercase character z and is connected
-- to its existential Boolean correctness contract. This file contains no proof.

{-# OPTIONS --safe #-}

module VerinaBasic14 where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Char using (Char; primCharEquality)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String; primStringToList)

infix 2 _↔_
infixr 3 _∨_
infixr 4 _∧_
infix 4 _∈_
infixr 5 _||_

record Top : Set where
  constructor top

record _∧_ (A B : Set) : Set where
  constructor both
  field
    first : A
    second : B

data _∨_ (A B : Set) : Set where
  left : A → A ∨ B
  right : B → A ∨ B

record _↔_ (A B : Set) : Set where
  constructor iff
  field
    forward : A → B
    backward : B → A

data Exists {A : Set} (P : A → Set) : Set where
  witness : (x : A) → P x → Exists P

data IsTrue : Bool → Set where
  true-witness : IsTrue true

data _∈_ {A : Set} (x : A) : List A → Set where
  here : {xs : List A} → x ∈ (x ∷ xs)
  there : {y : A} {xs : List A} → x ∈ xs → x ∈ (y ∷ xs)

_||_ : Bool → Bool → Bool
true || other = true
false || other = other

anyList : {A : Set} → (A → Bool) → List A → Bool
anyList predicate [] = false
anyList predicate (x ∷ xs) =
  predicate x || anyList predicate xs

containsZ-precond : String → Set
containsZ-precond s = Top

containsZ :
  (s : String) →
  containsZ-precond s →
  Bool
containsZ s h-precond =
  anyList
    (λ c →
      primCharEquality c 'z' ||
      primCharEquality c 'Z')
    (primStringToList s)

containsZ-postcond :
  (s : String) →
  (result : Bool) →
  containsZ-precond s →
  Set
containsZ-postcond s result h-precond =
  let characters = primStringToList s
  in
    Exists
      (λ x →
        (x ∈ characters) ∧
        ((x ≡ 'z') ∨ (x ≡ 'Z')))
    ↔ IsTrue result

containsZ-spec-satisfied : Set
containsZ-spec-satisfied =
  (s : String) →
  (h-precond : containsZ-precond s) →
  containsZ-postcond
    s
    (containsZ s h-precond)
    h-precond
