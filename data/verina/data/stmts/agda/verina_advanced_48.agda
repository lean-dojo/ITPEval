-- Statement-only formalization of VERINA corpus artifact verina_advanced_48,
-- catalog title "mergeSort": the source's deterministic insertion-sort
-- implementation returns the input integers in nondecreasing order as a
-- permutation. This file contains no proof.

{-# OPTIONS --safe #-}

module VerinaAdvanced48 where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Int using (Int; negsuc; pos)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc)

infixr 3 _∧_

record Top : Set where
  constructor top

record _∧_ (A B : Set) : Set where
  constructor both
  field
    first : A
    second : B

data IsTrue : Bool → Set where
  true-witness : IsTrue true

if_then_else_ : {A : Set} → Bool → A → A → A
if true then when-true else when-false = when-true
if false then when-true else when-false = when-false

natLessOrEqual : Nat → Nat → Bool
natLessOrEqual zero _ = true
natLessOrEqual (suc _) zero = false
natLessOrEqual (suc m) (suc n) = natLessOrEqual m n

intLessOrEqual : Int → Int → Bool
intLessOrEqual (pos m) (pos n) = natLessOrEqual m n
intLessOrEqual (pos _) (negsuc _) = false
intLessOrEqual (negsuc _) (pos _) = true
intLessOrEqual (negsuc m) (negsuc n) = natLessOrEqual n m

IntLessOrEqual : Int → Int → Set
IntLessOrEqual x y = IsTrue (intLessOrEqual x y)

All : {A : Set} → (A → Set) → List A → Set
All predicate [] = Top
All predicate (x ∷ xs) = predicate x ∧ All predicate xs

Pairwise :
  {A : Set} → (A → A → Set) → List A → Set
Pairwise relation [] = Top
Pairwise relation (x ∷ xs) =
  All (relation x) xs ∧ Pairwise relation xs

data Permutation {A : Set} : List A → List A → Set where
  permutationNil :
    Permutation [] []

  permutationSkip :
    {x : A} {xs ys : List A} →
    Permutation xs ys →
    Permutation (x ∷ xs) (x ∷ ys)

  permutationSwap :
    {x y : A} {xs : List A} →
    Permutation (y ∷ x ∷ xs) (x ∷ y ∷ xs)

  permutationTrans :
    {xs ys zs : List A} →
    Permutation xs ys →
    Permutation ys zs →
    Permutation xs zs

mergeSort-precond : List Int → Set
mergeSort-precond list = Top

insert : Int → List Int → List Int
insert x [] = x ∷ []
insert x (y ∷ ys) =
  if intLessOrEqual x y
  then (x ∷ y ∷ ys)
  else (y ∷ insert x ys)

sort : List Int → List Int
sort [] = []
sort (x ∷ xs) = insert x (sort xs)

mergeSort :
  (list : List Int) →
  mergeSort-precond list →
  List Int
mergeSort list h-precond = sort list

mergeSort-postcond :
  (list : List Int) →
  (result : List Int) →
  mergeSort-precond list →
  Set
mergeSort-postcond list result h-precond =
  Pairwise IntLessOrEqual result ∧ Permutation list result

mergeSort-spec-satisfied : Set
mergeSort-spec-satisfied =
  (list : List Int) →
  (h-precond : mergeSort-precond list) →
  mergeSort-postcond
    list
    (mergeSort list h-precond)
    h-precond
