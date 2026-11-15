-- Statement-only formalization of VERINA corpus artifact verina_advanced_73,
-- catalog title "smallestMissing": a deterministic recursive scan returns the
-- smallest natural number absent from a strictly increasing list and is
-- connected to its full correctness contract. This file contains no proof.

{-# OPTIONS --safe #-}

module VerinaAdvanced73 where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc)

infixr 3 _∧_
infix 4 _<_ _∈_

data Empty : Set where

Not : Set → Set
Not A = A → Empty

record Top : Set where
  constructor top

record _∧_ (A B : Set) : Set where
  constructor both
  field
    first : A
    second : B

data _<_ : Nat → Nat → Set where
  zero<succ : {n : Nat} → zero < suc n
  succ<succ : {m n : Nat} → m < n → suc m < suc n

data _∈_ (x : Nat) : List Nat → Set where
  here : {xs : List Nat} → x ∈ (x ∷ xs)
  there : {y : Nat} {xs : List Nat} → x ∈ xs → x ∈ (y ∷ xs)

if_then_else_ : {A : Set} → Bool → A → A → A
if true then when-true else when-false = when-true
if false then when-true else when-false = when-false

natEqual : Nat → Nat → Bool
natEqual zero zero = true
natEqual zero (suc _) = false
natEqual (suc _) zero = false
natEqual (suc m) (suc n) = natEqual m n

natLess : Nat → Nat → Bool
natLess zero zero = false
natLess zero (suc _) = true
natLess (suc _) zero = false
natLess (suc m) (suc n) = natLess m n

All : {A : Set} → (A → Set) → List A → Set
All predicate [] = Top
All predicate (x ∷ xs) =
  predicate x ∧ All predicate xs

Pairwise :
  {A : Set} → (A → A → Set) → List A → Set
Pairwise relation [] = Top
Pairwise relation (x ∷ xs) =
  All (relation x) xs ∧ Pairwise relation xs

smallestMissing-precond : List Nat → Set
smallestMissing-precond l =
  Pairwise _<_ l

search : List Nat → Nat → Nat
search [] n = n
search (x ∷ xs) n =
  if natEqual x n
  then search xs (suc n)
  else
    if natLess n x
    then n
    else search xs n

smallestMissing :
  (l : List Nat) →
  smallestMissing-precond l →
  Nat
smallestMissing l h-precond =
  search l zero

smallestMissing-postcond :
  (l : List Nat) →
  (result : Nat) →
  smallestMissing-precond l →
  Set
smallestMissing-postcond l result h-precond =
  Not (result ∈ l) ∧
  ((candidate : Nat) →
    candidate < result →
    candidate ∈ l)

smallestMissing-spec-satisfied : Set
smallestMissing-spec-satisfied =
  (l : List Nat) →
  (h-precond : smallestMissing-precond l) →
  smallestMissing-postcond
    l
    (smallestMissing l h-precond)
    h-precond
