-- Statement-only formalization of VERINA corpus artifact verina_advanced_50,
-- catalog title "mergeSorted": a deterministic program merges two
-- nondecreasing natural-number arrays into a nondecreasing permutation of
-- their concatenation. This file contains no proof.

{-# OPTIONS --safe #-}

module VerinaAdvanced50 where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)

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

NatLessOrEqual : Nat → Nat → Set
NatLessOrEqual m n = IsTrue (natLessOrEqual m n)

listLength : {A : Set} → List A → Nat
listLength [] = zero
listLength (_ ∷ xs) = suc (listLength xs)

appendList : {A : Set} → List A → List A → List A
appendList [] ys = ys
appendList (x ∷ xs) ys = x ∷ appendList xs ys

snoc : {A : Set} → List A → A → List A
snoc xs x = appendList xs (x ∷ [])

dropList : {A : Set} → Nat → List A → List A
dropList zero xs = xs
dropList (suc n) [] = []
dropList (suc n) (_ ∷ xs) = dropList n xs

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

mergeSorted-precond :
  List Nat → List Nat → Set
mergeSorted-precond a1 a2 =
  Pairwise NatLessOrEqual a1 ∧
  Pairwise NatLessOrEqual a2

record MergeState : Set where
  constructor merge-state
  field
    firstIndex : Nat
    secondIndex : Nat
    mergedResult : List Nat

open MergeState public

mergeLoopWithFuel :
  Nat →
  List Nat →
  List Nat →
  Nat →
  Nat →
  List Nat →
  MergeState
mergeLoopWithFuel zero xs ys i j result =
  merge-state i j result
mergeLoopWithFuel (suc fuel) [] ys i j result =
  merge-state i j result
mergeLoopWithFuel (suc fuel) xs [] i j result =
  merge-state i j result
mergeLoopWithFuel
  (suc fuel)
  (x ∷ xs)
  (y ∷ ys)
  i
  j
  result =
    if natLessOrEqual x y
    then
      mergeLoopWithFuel
        fuel
        xs
        (y ∷ ys)
        (suc i)
        j
        (snoc result x)
    else
      mergeLoopWithFuel
        fuel
        (x ∷ xs)
        ys
        i
        (suc j)
        (snoc result y)

mergeLoop :
  List Nat →
  List Nat →
  Nat →
  Nat →
  List Nat →
  MergeState
mergeLoop a1 a2 i j result =
  let remaining1 = dropList i a1
      remaining2 = dropList j a2
  in
    mergeLoopWithFuel
      (listLength remaining1 + listLength remaining2)
      remaining1
      remaining2
      i
      j
      result

drainFrom :
  List Nat →
  List Nat →
  List Nat
drainFrom [] result = result
drainFrom (x ∷ xs) result =
  drainFrom xs (snoc result x)

drain :
  List Nat →
  Nat →
  List Nat →
  List Nat
drain array i result =
  drainFrom (dropList i array) result

mergeSorted :
  (a1 a2 : List Nat) →
  mergeSorted-precond a1 a2 →
  List Nat
mergeSorted a1 a2 h-precond =
  let state = mergeLoop a1 a2 zero zero []
      after-first =
        drain a1 (firstIndex state) (mergedResult state)
  in
    drain a2 (secondIndex state) after-first

mergeSorted-postcond :
  (a1 a2 : List Nat) →
  (result : List Nat) →
  mergeSorted-precond a1 a2 →
  Set
mergeSorted-postcond a1 a2 result h-precond =
  Pairwise NatLessOrEqual result ∧
  Permutation result (appendList a1 a2)

mergeSorted-spec-satisfied : Set
mergeSorted-spec-satisfied =
  (a1 a2 : List Nat) →
  (h-precond : mergeSorted-precond a1 a2) →
  mergeSorted-postcond
    a1
    a2
    (mergeSorted a1 a2 h-precond)
    h-precond
