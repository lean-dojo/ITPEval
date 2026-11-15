-- Statement-only formalization of VERINA corpus artifact verina_advanced_81,
-- catalog title "uniqueSorted": a deterministic duplicate-removal and
-- insertion-sort program returns a permutation of the input's distinct
-- integers in nondecreasing order. This file contains no proof.

{-# OPTIONS --safe #-}

module VerinaAdvanced81 where

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

natEqual : Nat → Nat → Bool
natEqual zero zero = true
natEqual zero (suc _) = false
natEqual (suc _) zero = false
natEqual (suc m) (suc n) = natEqual m n

natLessOrEqual : Nat → Nat → Bool
natLessOrEqual zero _ = true
natLessOrEqual (suc _) zero = false
natLessOrEqual (suc m) (suc n) = natLessOrEqual m n

intEqual : Int → Int → Bool
intEqual (pos m) (pos n) = natEqual m n
intEqual (pos _) (negsuc _) = false
intEqual (negsuc _) (pos _) = false
intEqual (negsuc m) (negsuc n) = natEqual m n

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

containsInt : Int → List Int → Bool
containsInt sought [] = false
containsInt sought (x ∷ xs) =
  if intEqual sought x
  then true
  else containsInt sought xs

reverseOnto : {A : Set} → List A → List A → List A
reverseOnto [] accumulator = accumulator
reverseOnto (x ∷ xs) accumulator =
  reverseOnto xs (x ∷ accumulator)

reverseList : {A : Set} → List A → List A
reverseList xs = reverseOnto xs []

removeDupsAux :
  List Int →
  List Int →
  List Int →
  List Int
removeDupsAux [] seen accumulator =
  reverseList accumulator
removeDupsAux (x ∷ xs) seen accumulator =
  if containsInt x seen
  then removeDupsAux xs seen accumulator
  else removeDupsAux xs (x ∷ seen) (x ∷ accumulator)

removeDups : List Int → List Int
removeDups xs = removeDupsAux xs [] []

insert : Int → List Int → List Int
insert x [] = x ∷ []
insert x (head ∷ tail) =
  if intLessOrEqual x head
  then (x ∷ head ∷ tail)
  else (head ∷ insert x tail)

insertionSort : List Int → List Int
insertionSort [] = []
insertionSort (head ∷ tail) =
  insert head (insertionSort tail)

eraseDups : List Int → List Int
eraseDups [] = []
eraseDups (x ∷ xs) =
  if containsInt x xs
  then eraseDups xs
  else (x ∷ eraseDups xs)

uniqueSorted-precond : List Int → Set
uniqueSorted-precond arr = Top

uniqueSorted :
  (arr : List Int) →
  uniqueSorted-precond arr →
  List Int
uniqueSorted arr h-precond =
  insertionSort (removeDups arr)

uniqueSorted-postcond :
  (arr : List Int) →
  (result : List Int) →
  uniqueSorted-precond arr →
  Set
uniqueSorted-postcond arr result h-precond =
  Permutation (eraseDups arr) result ∧
  Pairwise IntLessOrEqual result

uniqueSorted-spec-satisfied : Set
uniqueSorted-spec-satisfied =
  (arr : List Int) →
  (h-precond : uniqueSorted-precond arr) →
  uniqueSorted-postcond
    arr
    (uniqueSorted arr h-precond)
    h-precond
