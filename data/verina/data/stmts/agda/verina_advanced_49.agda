-- Statement-only formalization of VERINA corpus artifact verina_advanced_49,
-- catalog title "mergeSortedLists": a deterministic merge program combines two
-- nondecreasing integer lists into a nondecreasing permutation of their
-- concatenation. This file contains no proof.

{-# OPTIONS --safe #-}

module VerinaAdvanced49 where

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

natAdd : Nat → Nat → Nat
natAdd zero n = n
natAdd (suc m) n = suc (natAdd m n)

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

listLength : {A : Set} → List A → Nat
listLength [] = zero
listLength (_ ∷ xs) = suc (listLength xs)

appendList : {A : Set} → List A → List A → List A
appendList [] ys = ys
appendList (x ∷ xs) ys = x ∷ appendList xs ys

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

mergeSortedLists-precond :
  List Int → List Int → Set
mergeSortedLists-precond arr1 arr2 =
  Pairwise IntLessOrEqual arr1 ∧
  Pairwise IntLessOrEqual arr2

mergeWithFuel :
  Nat → List Int → List Int → List Int
mergeWithFuel zero xs ys = appendList xs ys
mergeWithFuel (suc fuel) [] ys = ys
mergeWithFuel (suc fuel) xs [] = xs
mergeWithFuel (suc fuel) (x ∷ xt) (y ∷ yt) =
  if intLessOrEqual x y
  then (x ∷ mergeWithFuel fuel xt (y ∷ yt))
  else (y ∷ mergeWithFuel fuel (x ∷ xt) yt)

merge : List Int → List Int → List Int
merge xs ys =
  mergeWithFuel
    (natAdd (listLength xs) (listLength ys))
    xs
    ys

mergeSortedLists :
  (arr1 arr2 : List Int) →
  mergeSortedLists-precond arr1 arr2 →
  List Int
mergeSortedLists arr1 arr2 h-precond = merge arr1 arr2

mergeSortedLists-postcond :
  (arr1 arr2 : List Int) →
  (result : List Int) →
  mergeSortedLists-precond arr1 arr2 →
  Set
mergeSortedLists-postcond arr1 arr2 result h-precond =
  Pairwise IntLessOrEqual result ∧
  Permutation (appendList arr1 arr2) result

mergeSortedLists-spec-satisfied : Set
mergeSortedLists-spec-satisfied =
  (arr1 arr2 : List Int) →
  (h-precond : mergeSortedLists-precond arr1 arr2) →
  mergeSortedLists-postcond
    arr1
    arr2
    (mergeSortedLists arr1 arr2 h-precond)
    h-precond
