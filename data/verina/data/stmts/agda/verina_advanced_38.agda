-- Statement-only formalization of VERINA corpus artifact verina_advanced_38,
-- catalog title "maxCoverageAfterRemovingOne": a deterministic program removes
-- each interval in turn, stably sorts and merges the remainder, and returns a
-- maximum natural-number coverage with its maximizing contract. This file
-- contains no proof.

{-# OPTIONS --safe #-}

module VerinaAdvanced38 where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)

infix 4 _≤_ _<_

data _≤_ : Nat → Nat → Set where
  zero≤ : {n : Nat} → zero ≤ n
  suc≤suc : {m n : Nat} → m ≤ n → suc m ≤ suc n

_<_ : Nat → Nat → Set
m < n = suc m ≤ n

if_then_else_ : {A : Set} → Bool → A → A → A
if true then when-true else when-false = when-true
if false then when-true else when-false = when-false

natLess : Nat → Nat → Bool
natLess zero zero = false
natLess zero (suc _) = true
natLess (suc _) zero = false
natLess (suc m) (suc n) = natLess m n

natLessOrEqual : Nat → Nat → Bool
natLessOrEqual zero _ = true
natLessOrEqual (suc _) zero = false
natLessOrEqual (suc m) (suc n) = natLessOrEqual m n

natSubtract : Nat → Nat → Nat
natSubtract m zero = m
natSubtract zero (suc n) = zero
natSubtract (suc m) (suc n) = natSubtract m n

natMax : Nat → Nat → Nat
natMax m n =
  if natLess m n
  then n
  else m

one : Nat
one = suc zero

record NatPair : Set where
  constructor pair
  field
    pairFirst : Nat
    pairSecond : Nat

open NatPair public

listLength : {A : Set} → List A → Nat
listLength [] = zero
listLength (_ ∷ xs) = suc (listLength xs)

appendList : {A : Set} → List A → List A → List A
appendList [] ys = ys
appendList (x ∷ xs) ys = x ∷ appendList xs ys

takeList : {A : Set} → Nat → List A → List A
takeList zero xs = []
takeList (suc n) [] = []
takeList (suc n) (x ∷ xs) = x ∷ takeList n xs

dropList : {A : Set} → Nat → List A → List A
dropList zero xs = xs
dropList (suc n) [] = []
dropList (suc n) (_ ∷ xs) = dropList n xs

reverseOnto : {A : Set} → List A → List A → List A
reverseOnto accumulator [] = accumulator
reverseOnto accumulator (x ∷ xs) =
  reverseOnto (x ∷ accumulator) xs

reverseList : {A : Set} → List A → List A
reverseList xs = reverseOnto [] xs

foldLeft : {A B : Set} → (A → B → A) → A → List B → A
foldLeft step accumulator [] = accumulator
foldLeft step accumulator (x ∷ xs) =
  foldLeft step (step accumulator x) xs

rangeFrom : Nat → Nat → List Nat
rangeFrom start zero = []
rangeFrom start (suc count) =
  start ∷ rangeFrom (suc start) count

range : Nat → List Nat
range count = rangeFrom zero count

eraseIndex : {A : Set} → List A → Nat → List A
eraseIndex [] index = []
eraseIndex (x ∷ xs) zero = xs
eraseIndex (x ∷ xs) (suc index) =
  x ∷ eraseIndex xs index

ceilHalf : Nat → Nat
ceilHalf zero = zero
ceilHalf (suc zero) = suc zero
ceilHalf (suc (suc n)) = suc (ceilHalf n)

mergeIntervalsWithFuel :
  Nat →
  List NatPair →
  List NatPair →
  List NatPair
mergeIntervalsWithFuel zero xs ys = appendList xs ys
mergeIntervalsWithFuel (suc fuel) [] ys = ys
mergeIntervalsWithFuel (suc fuel) xs [] = xs
mergeIntervalsWithFuel
  (suc fuel)
  (x ∷ xs)
  (y ∷ ys) =
    if natLessOrEqual (pairFirst x) (pairFirst y)
    then
      (x ∷
      mergeIntervalsWithFuel fuel xs (y ∷ ys))
    else
      (y ∷
      mergeIntervalsWithFuel fuel (x ∷ xs) ys)

mergeIntervals :
  List NatPair →
  List NatPair →
  List NatPair
mergeIntervals xs ys =
  mergeIntervalsWithFuel
    (listLength xs + listLength ys)
    xs
    ys

mergeSortIntervalsWithFuel :
  Nat →
  List NatPair →
  List NatPair
mergeSortIntervalsWithFuel zero xs = xs
mergeSortIntervalsWithFuel (suc fuel) [] = []
mergeSortIntervalsWithFuel (suc fuel) (x ∷ []) = x ∷ []
mergeSortIntervalsWithFuel
  (suc fuel)
  xs@(x ∷ y ∷ rest) =
    let cut = ceilHalf (listLength xs)
        left = takeList cut xs
        right = dropList cut xs
    in
      mergeIntervals
        (mergeSortIntervalsWithFuel fuel left)
        (mergeSortIntervalsWithFuel fuel right)

mergeSortIntervals : List NatPair → List NatPair
mergeSortIntervals xs =
  mergeSortIntervalsWithFuel (listLength xs) xs

mergeStep :
  List NatPair →
  NatPair →
  List NatPair
mergeStep [] current = current ∷ []
mergeStep (pair start finish ∷ rest) current =
  if natLessOrEqual (pairFirst current) finish
  then
    (pair start (natMax finish (pairSecond current)) ∷ rest)
  else
    (current ∷ pair start finish ∷ rest)

mergedIntervals : List NatPair → List NatPair
mergedIntervals intervals =
  foldLeft mergeStep [] (mergeSortIntervals intervals)

coverageStep : Nat → NatPair → Nat
coverageStep accumulator (pair start finish) =
  accumulator + natSubtract finish start

coverage : List NatPair → Nat
coverage intervals =
  foldLeft
    coverageStep
    zero
    (reverseList (mergedIntervals intervals))

coverageAfterRemoving :
  List NatPair →
  Nat →
  Nat
coverageAfterRemoving intervals index =
  coverage (eraseIndex intervals index)

maxCoverageAfterRemovingOne-precond :
  List NatPair →
  Set
maxCoverageAfterRemovingOne-precond intervals =
  zero < listLength intervals

maximumStep :
  List NatPair →
  Nat →
  Nat →
  Nat
maximumStep intervals accumulator index =
  natMax
    accumulator
    (coverageAfterRemoving intervals index)

maxCoverageAfterRemovingOne :
  (intervals : List NatPair) →
  maxCoverageAfterRemovingOne-precond intervals →
  Nat
maxCoverageAfterRemovingOne intervals h-precond =
  let n = listLength intervals
  in
    if natLessOrEqual n one
    then zero
    else
      foldLeft
        (maximumStep intervals)
        zero
        (range n)

record
  MaximumCoverageWitness
    (intervals : List NatPair)
    (result : Nat) : Set
  where
  constructor maximum-witness
  field
    removed-index : Nat
    index-in-bounds :
      removed-index < listLength intervals
    result-is-coverage :
      result ≡
      coverageAfterRemoving intervals removed-index
    greatest-coverage :
      (other-index : Nat) →
      other-index < listLength intervals →
      coverageAfterRemoving intervals other-index ≤
      coverageAfterRemoving intervals removed-index

maxCoverageAfterRemovingOne-postcond :
  (intervals : List NatPair) →
  (result : Nat) →
  maxCoverageAfterRemovingOne-precond intervals →
  Set
maxCoverageAfterRemovingOne-postcond
  intervals
  result
  h-precond =
    MaximumCoverageWitness intervals result

maxCoverageAfterRemovingOne-spec-satisfied : Set
maxCoverageAfterRemovingOne-spec-satisfied =
  (intervals : List NatPair) →
  (h-precond :
    maxCoverageAfterRemovingOne-precond intervals) →
  maxCoverageAfterRemovingOne-postcond
    intervals
    (maxCoverageAfterRemovingOne intervals h-precond)
    h-precond
