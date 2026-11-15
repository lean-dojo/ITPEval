-- Statement-only formalization of VERINA corpus artifact verina_advanced_16,
-- catalog title "insertionSort": a deterministic insertion-sort program returns
-- the input integers in ascending order as a permutation. This file contains no proof.

{-# OPTIONS --safe #-}

module VerinaAdvanced16 where

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

insertionSort-precond : List Int → Set
insertionSort-precond xs = Top

insert : Int → List Int → List Int
insert x [] = x ∷ []
insert x (y ∷ ys) =
  if intLessOrEqual x y
  then (x ∷ y ∷ ys)
  else (y ∷ insert x ys)

sort : List Int → List Int
sort [] = []
sort (x ∷ xs) = insert x (sort xs)

insertionSort :
  (xs : List Int) →
  insertionSort-precond xs →
  List Int
insertionSort xs h-precond = sort xs

insertionSort-postcond :
  (xs : List Int) →
  (result : List Int) →
  insertionSort-precond xs →
  Set
insertionSort-postcond xs result h-precond =
  Pairwise IntLessOrEqual result ∧ Permutation xs result

insertionSort-spec-satisfied : Set
insertionSort-spec-satisfied =
  (xs : List Int) →
  (h-precond : insertionSort-precond xs) →
  insertionSort-postcond
    xs
    (insertionSort xs h-precond)
    h-precond
