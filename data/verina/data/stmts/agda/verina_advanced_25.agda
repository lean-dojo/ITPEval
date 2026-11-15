-- Statement-only formalization of VERINA corpus artifact verina_advanced_25,
-- catalog title "lengthOfLIS": a deterministic dynamic-programming program
-- computes the longest strictly increasing subsequence length, characterized
-- by exhaustive subsequence enumeration. This file contains no proof.

{-# OPTIONS --safe #-}

module VerinaAdvanced25 where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Int using (Int; negsuc; pos)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)

infixr 3 _∧_
infixr 5 _&&_

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

_&&_ : Bool → Bool → Bool
true && other = other
false && other = false

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

intLess : Int → Int → Bool
intLess (pos m) (pos n) = natLess m n
intLess (pos _) (negsuc _) = false
intLess (negsuc _) (pos _) = true
intLess (negsuc m) (negsuc n) = natLess n m

one : Nat
one = suc zero

listIsEmpty : {A : Set} → List A → Bool
listIsEmpty [] = true
listIsEmpty (_ ∷ _) = false

listLength : {A : Set} → List A → Nat
listLength [] = zero
listLength (_ ∷ xs) = suc (listLength xs)

appendList : {A : Set} → List A → List A → List A
appendList [] ys = ys
appendList (x ∷ xs) ys = x ∷ appendList xs ys

mapList : {A B : Set} → (A → B) → List A → List B
mapList f [] = []
mapList f (x ∷ xs) = f x ∷ mapList f xs

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

reverseOnto : {A : Set} → List A → List A → List A
reverseOnto accumulator [] = accumulator
reverseOnto accumulator (x ∷ xs) =
  reverseOnto (x ∷ accumulator) xs

reverseList : {A : Set} → List A → List A
reverseList xs = reverseOnto [] xs

repeatList : {A : Set} → Nat → A → List A
repeatList zero value = []
repeatList (suc n) value = value ∷ repeatList n value

nthDefault : {A : Set} → A → Nat → List A → A
nthDefault default zero [] = default
nthDefault default zero (x ∷ xs) = x
nthDefault default (suc n) [] = default
nthDefault default (suc n) (_ ∷ xs) =
  nthDefault default n xs

setNth : {A : Set} → Nat → A → List A → List A
setNth zero value [] = []
setNth zero value (_ ∷ xs) = value ∷ xs
setNth (suc n) value [] = []
setNth (suc n) value (x ∷ xs) =
  x ∷ setNth n value xs

rangeFrom : Nat → Nat → List Nat
rangeFrom start zero = []
rangeFrom start (suc count) =
  start ∷ rangeFrom (suc start) count

range : Nat → List Nat
range count = rangeFrom zero count

allList : {A : Set} → (A → Bool) → List A → Bool
allList predicate [] = true
allList predicate (x ∷ xs) =
  if predicate x
  then allList predicate xs
  else false

containsNat : Nat → List Nat → Bool
containsNat sought [] = false
containsNat sought (x ∷ xs) =
  if natEqual sought x
  then true
  else containsNat sought xs

lengthOfLIS-precond : List Int → Set
lengthOfLIS-precond nums = Top

maxNat : Nat → Nat → Nat
maxNat a b =
  if natLess a b then b else a

maxInArray : List Nat → Nat
maxInArray arr = foldLeft maxNat zero arr

updateDPEntry :
  List Int →
  Nat →
  List Nat →
  Nat →
  List Nat
updateDPEntry nums i dp j =
  let candidate = suc (nthDefault zero j dp)
      current = nthDefault zero i dp
  in
    if
      intLess
        (nthDefault (pos zero) j nums)
        (nthDefault (pos zero) i nums)
      && natLess current candidate
    then setNth i candidate dp
    else dp

updateDPIndex :
  List Int →
  List Nat →
  Nat →
  List Nat
updateDPIndex nums dp i =
  foldLeft
    (updateDPEntry nums i)
    dp
    (range i)

buildDP : List Int → List Nat
buildDP nums =
  let n = listLength nums
      initial = repeatList n one
  in
    foldLeft
      (updateDPIndex nums)
      initial
      (rangeFrom one (natSubtract n one))

lengthOfLIS :
  (nums : List Int) →
  lengthOfLIS-precond nums →
  Nat
lengthOfLIS nums h-precond =
  if listIsEmpty nums
  then zero
  else maxInArray (buildDP nums)

allSubseqStep :
  List (List Int) →
  Int →
  List (List Int)
allSubseqStep accumulator x =
  appendList
    accumulator
    (mapList (λ subsequence → x ∷ subsequence) accumulator)

allSubseq : List Int → List (List Int)
allSubseq nums =
  mapList
    reverseList
    (foldLeft allSubseqStep ([] ∷ []) nums)

isStrictlyIncreasing : List Int → Bool
isStrictlyIncreasing [] = true
isStrictlyIncreasing (_ ∷ []) = true
isStrictlyIncreasing (x ∷ y ∷ rest) =
  intLess x y && isStrictlyIncreasing (y ∷ rest)

increasingSubsequenceLengths : List Int → List Nat
increasingSubsequenceLengths nums =
  mapList
    listLength
    (filterList isStrictlyIncreasing (allSubseq nums))

lengthOfLIS-postcond :
  (nums : List Int) →
  (result : Nat) →
  lengthOfLIS-precond nums →
  Set
lengthOfLIS-postcond nums result h-precond =
  let lengths = increasingSubsequenceLengths nums
  in
    IsTrue (containsNat result lengths) ∧
    IsTrue (allList (λ length → natLessOrEqual length result) lengths)

lengthOfLIS-spec-satisfied : Set
lengthOfLIS-spec-satisfied =
  (nums : List Int) →
  (h-precond : lengthOfLIS-precond nums) →
  lengthOfLIS-postcond
    nums
    (lengthOfLIS nums h-precond)
    h-precond
