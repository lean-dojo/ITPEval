-- Statement-only formalization of VERINA corpus artifact verina_advanced_29,
-- catalog title "longestGoodSubarray": a deterministic sliding-window program
-- computes the maximum length among contiguous subarrays whose value
-- frequencies are at most a positive bound. This file contains no proof.

{-# OPTIONS --safe #-}

module VerinaAdvanced29 where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)

infixr 2 _∨_
infixr 3 _∧_
infix 4 _≤_ _<_

data Empty : Set where

Not : Set → Set
Not A = A → Empty

record _∧_ (A B : Set) : Set where
  constructor both
  field
    first : A
    second : B

data _∨_ (A B : Set) : Set where
  or-left : A → A ∨ B
  or-right : B → A ∨ B

data _≤_ : Nat → Nat → Set where
  zero≤ : {n : Nat} → zero ≤ n
  suc≤suc : {m n : Nat} → m ≤ n → suc m ≤ suc n

_<_ : Nat → Nat → Set
m < n = suc m ≤ n

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

listLength : {A : Set} → List A → Nat
listLength [] = zero
listLength (_ ∷ xs) = suc (listLength xs)

appendList : {A : Set} → List A → List A → List A
appendList [] ys = ys
appendList (x ∷ xs) ys = x ∷ appendList xs ys

mapList : {A B : Set} → (A → B) → List A → List B
mapList f [] = []
mapList f (x ∷ xs) = f x ∷ mapList f xs

flatMapList : {A B : Set} → (A → List B) → List A → List B
flatMapList f [] = []
flatMapList f (x ∷ xs) =
  appendList (f x) (flatMapList f xs)

filterList : {A : Set} → (A → Bool) → List A → List A
filterList predicate [] = []
filterList predicate (x ∷ xs) =
  if predicate x
  then x ∷ filterList predicate xs
  else filterList predicate xs

foldLeft : {A B : Set} → (A → B → A) → A → List B → A
foldLeft step accumulator [] = accumulator
foldLeft step accumulator (x ∷ xs) =
  foldLeft step (step accumulator x) xs

allList : {A : Set} → (A → Bool) → List A → Bool
allList predicate [] = true
allList predicate (x ∷ xs) =
  if predicate x
  then allList predicate xs
  else false

anyList : {A : Set} → (A → Bool) → List A → Bool
anyList predicate [] = false
anyList predicate (x ∷ xs) =
  if predicate x
  then true
  else anyList predicate xs

takeList : {A : Set} → Nat → List A → List A
takeList zero xs = []
takeList (suc n) [] = []
takeList (suc n) (x ∷ xs) = x ∷ takeList n xs

dropList : {A : Set} → Nat → List A → List A
dropList zero xs = xs
dropList (suc n) [] = []
dropList (suc n) (_ ∷ xs) = dropList n xs

nthDefault : {A : Set} → A → Nat → List A → A
nthDefault default zero [] = default
nthDefault default zero (x ∷ xs) = x
nthDefault default (suc n) [] = default
nthDefault default (suc n) (_ ∷ xs) =
  nthDefault default n xs

rangeFrom : Nat → Nat → List Nat
rangeFrom start zero = []
rangeFrom start (suc count) =
  start ∷ rangeFrom (suc start) count

range : Nat → List Nat
range count = rangeFrom zero count

countNat : Nat → List Nat → Nat
countNat sought [] = zero
countNat sought (x ∷ xs) =
  if natEqual sought x
  then suc (countNat sought xs)
  else countNat sought xs

record Entry : Set where
  constructor entry
  field
    entryKey : Nat
    entryValue : Nat

FrequencyTable : Set
FrequencyTable = List Entry

lookupCount : Nat → FrequencyTable → Nat
lookupCount key [] = zero
lookupCount key (entry stored-key value ∷ rest) =
  if natEqual key stored-key
  then value
  else lookupCount key rest

insertCount : Nat → Nat → FrequencyTable → FrequencyTable
insertCount key value [] = entry key value ∷ []
insertCount key value (entry stored-key stored-value ∷ rest) =
  if natEqual key stored-key
  then (entry key value ∷ rest)
  else (entry stored-key stored-value ∷ insertCount key value rest)

eraseCount : Nat → FrequencyTable → FrequencyTable
eraseCount key [] = []
eraseCount key (entry stored-key value ∷ rest) =
  if natEqual key stored-key
  then rest
  else (entry stored-key value ∷ eraseCount key rest)

anyCountGreater : Nat → FrequencyTable → Bool
anyCountGreater bound [] = false
anyCountGreater bound (entry key value ∷ rest) =
  if natLess bound value
  then true
  else anyCountGreater bound rest

longestGoodSubarray-precond : List Nat → Nat → Set
longestGoodSubarray-precond nums k = zero < k

record WindowState : Set where
  constructor window
  field
    leftIndex : Nat
    maximumLength : Nat
    frequencyTable : FrequencyTable

open WindowState

shrinkOnce : List Nat → WindowState → WindowState
shrinkOnce nums (window left maximum frequencies) =
  let left-value = nthDefault zero left nums
      left-count = lookupCount left-value frequencies
      reduced-frequencies =
        if natEqual left-count (suc zero)
        then eraseCount left-value frequencies
        else
          insertCount
            left-value
            (natSubtract left-count (suc zero))
            frequencies
  in window (suc left) maximum reduced-frequencies

shrinkWindow :
  Nat →
  List Nat →
  Nat →
  WindowState →
  WindowState
shrinkWindow zero nums k state = state
shrinkWindow
  (suc fuel)
  nums
  k
  (window left maximum frequencies) =
    if anyCountGreater k frequencies
    then
      shrinkWindow
        fuel
        nums
        k
        (shrinkOnce nums (window left maximum frequencies))
    else window left maximum frequencies

processRight :
  List Nat →
  Nat →
  WindowState →
  Nat →
  WindowState
processRight nums k (window left maximum frequencies) right-index =
  let current-value = nthDefault zero right-index nums
      current-count = lookupCount current-value frequencies
      increased-frequencies =
        insertCount current-value (suc current-count) frequencies
      shrunk =
        shrinkWindow
          (listLength nums)
          nums
          k
          (window left maximum increased-frequencies)
      current-length =
        suc (natSubtract right-index (leftIndex shrunk))
  in
    window
      (leftIndex shrunk)
      (natMax (maximumLength shrunk) current-length)
      (frequencyTable shrunk)

longestGoodSubarray :
  (nums : List Nat) →
  (k : Nat) →
  longestGoodSubarray-precond nums k →
  Nat
longestGoodSubarray nums k h-precond =
  maximumLength
    (foldLeft
      (processRight nums k)
      (window zero zero [])
      (range (listLength nums)))

allSubarrays : List Nat → List (List Nat)
allSubarrays nums =
  let n = listLength nums
  in
    flatMapList
      (λ start →
        mapList
          (λ length → takeList length (dropList start nums))
          (range (suc (natSubtract n start))))
      (range (suc n))

subarrayFrequencies : List Nat → List (List Nat)
subarrayFrequencies nums =
  mapList
    (λ subarray →
      mapList (λ x → countNat x subarray) subarray)
    (allSubarrays nums)

validSubarrayFrequencies : List Nat → Nat → List (List Nat)
validSubarrayFrequencies nums k =
  filterList
    (λ frequencies →
      allList (λ count → natLessOrEqual count k) frequencies)
    (subarrayFrequencies nums)

longestGoodSubarray-postcond :
  (nums : List Nat) →
  (k : Nat) →
  (result : Nat) →
  longestGoodSubarray-precond nums k →
  Set
longestGoodSubarray-postcond nums k result h-precond =
  let valid = validSubarrayFrequencies nums k
  in
    ((nums ≡ []) ∧ (result ≡ zero)) ∨
    (Not (nums ≡ []) ∧
      IsTrue
        (anyList
          (λ frequencies →
            natEqual (listLength frequencies) result)
          valid) ∧
      IsTrue
        (allList
          (λ frequencies →
            natLessOrEqual (listLength frequencies) result)
          valid))

longestGoodSubarray-spec-satisfied : Set
longestGoodSubarray-spec-satisfied =
  (nums : List Nat) →
  (k : Nat) →
  (h-precond : longestGoodSubarray-precond nums k) →
  longestGoodSubarray-postcond
    nums
    k
    (longestGoodSubarray nums k h-precond)
    h-precond
