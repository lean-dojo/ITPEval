-- Statement-only formalization of VERINA corpus artifact verina_basic_33,
-- catalog title "smallestMissingNumber": a deterministic recursive scan of a
-- nondecreasing natural-number list returns the least natural number absent
-- from the list and is connected to that correctness contract. This file
-- contains no proof.

{-# OPTIONS --safe #-}

module VerinaBasic33 where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc)

infixr 3 _∧_
infix 4 _≤_ _<_ _∈_

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

data _≤_ : Nat → Nat → Set where
  zero≤ : {n : Nat} → zero ≤ n
  suc≤suc : {m n : Nat} → m ≤ n → suc m ≤ suc n

_<_ : Nat → Nat → Set
m < n = suc m ≤ n

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
All predicate (x ∷ xs) = predicate x ∧ All predicate xs

Pairwise :
  {A : Set} → (A → A → Set) → List A → Set
Pairwise relation [] = Top
Pairwise relation (x ∷ xs) =
  All (relation x) xs ∧ Pairwise relation xs

data _∈_ (x : Nat) : List Nat → Set where
  here : {xs : List Nat} → x ∈ (x ∷ xs)
  there : {y : Nat} {xs : List Nat} → x ∈ xs → x ∈ (y ∷ xs)

smallestMissingNumber-precond : List Nat → Set
smallestMissingNumber-precond s = Pairwise _≤_ s

findMissing : Nat → List Nat → Nat
findMissing v [] = v
findMissing v (x ∷ xs) =
  if natLess v x
  then v
  else
    if natEqual x v
    then findMissing (suc v) xs
    else findMissing v xs

smallestMissingNumber :
  (s : List Nat) →
  smallestMissingNumber-precond s →
  Nat
smallestMissingNumber s h-precond =
  findMissing zero s

smallestMissingNumber-postcond :
  (s : List Nat) →
  (result : Nat) →
  smallestMissingNumber-precond s →
  Set
smallestMissingNumber-postcond s result h-precond =
  Not (result ∈ s) ∧
  ((k : Nat) → k < result → k ∈ s)

smallestMissingNumber-spec-satisfied : Set
smallestMissingNumber-spec-satisfied =
  (s : List Nat) →
  (h-precond : smallestMissingNumber-precond s) →
  smallestMissingNumber-postcond
    s
    (smallestMissingNumber s h-precond)
    h-precond
