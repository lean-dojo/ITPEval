-- Statement-only formalization of VERINA corpus artifact verina_advanced_34,
-- catalog title "longestIncreasingSubsequence": a deterministic patience-sorting
-- program uses left-bound binary search to compute the longest strictly increasing
-- integer subsequence length and is connected to its maximality contract.
-- This file contains no proof.

{-# OPTIONS --safe #-}

module VerinaAdvanced34 where

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

notBool : Bool → Bool
notBool true = false
notBool false = true

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

natSubtract : Nat → Nat → Nat
natSubtract m zero = m
natSubtract zero (suc n) = zero
natSubtract (suc m) (suc n) = natSubtract m n

half : Nat → Nat
half zero = zero
half (suc zero) = zero
half (suc (suc n)) = suc (half n)

intEqual : Int → Int → Bool
intEqual (pos m) (pos n) = natEqual m n
intEqual (pos _) (negsuc _) = false
intEqual (negsuc _) (pos _) = false
intEqual (negsuc m) (negsuc n) = natEqual m n

intLess : Int → Int → Bool
intLess (pos m) (pos n) = natLess m n
intLess (pos _) (negsuc _) = false
intLess (negsuc _) (pos _) = true
intLess (negsuc m) (negsuc n) = natLess n m

intLessOrEqual : Int → Int → Bool
intLessOrEqual m n = notBool (intLess n m)

one : Nat
one = suc zero

zeroInt : Int
zeroInt = pos zero

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

allList : {A : Set} → (A → Bool) → List A → Bool
allList predicate [] = true
allList predicate (x ∷ xs) =
  if predicate x
  then allList predicate xs
  else false

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

containsInt : Int → List Int → Bool
containsInt sought [] = false
containsInt sought (x ∷ xs) =
  if intEqual sought x
  then true
  else containsInt sought xs

longestIncreasingSubsequence-precond : List Int → Set
longestIncreasingSubsequence-precond nums = Top

binarySearchLeftWithFuel :
  Nat →
  List Int →
  Int →
  Nat →
  Nat →
  Nat
binarySearchLeftWithFuel zero sub num left right = left
binarySearchLeftWithFuel (suc fuel) sub num left right
  with natLess left right
... | false = left
... | true with intEqual (nthDefault zeroInt (half (left + right)) sub) num
...   | true =
  binarySearchLeftWithFuel
    fuel
    sub
    num
    left
    (half (left + right))
...   | false with intLess (nthDefault zeroInt (half (left + right)) sub) num
...     | true =
  binarySearchLeftWithFuel
    fuel
    sub
    num
    (half (left + right) + one)
    right
...     | false =
  binarySearchLeftWithFuel
    fuel
    sub
    num
    left
    (half (left + right))

binarySearchLeft :
  List Int →
  Int →
  Nat →
  Nat →
  Nat
binarySearchLeft sub num left right =
  binarySearchLeftWithFuel
    (natSubtract right left)
    sub
    num
    left
    right

updateTails : List Int → Int → List Int
updateTails sub num =
  let last-index = natSubtract (listLength sub) one
      last-value = nthDefault zeroInt last-index sub
  in
    if intLess last-value num
    then appendList sub (num ∷ [])
    else
      let left = binarySearchLeft sub num zero last-index
      in setNth left num sub

buildTails : List Int → List Int → List Int
buildTails [] sub = sub
buildTails (num ∷ nums) sub =
  buildTails nums (updateTails sub num)

longestIncreasingSubsequence :
  (nums : List Int) →
  longestIncreasingSubsequence-precond nums →
  Int
longestIncreasingSubsequence [] h-precond = zeroInt
longestIncreasingSubsequence (head ∷ tail) h-precond =
  pos (listLength (buildTails tail (head ∷ [])))

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

pairwiseIntLess : List Int → Bool
pairwiseIntLess [] = true
pairwiseIntLess (x ∷ xs) =
  allList (intLess x) xs && pairwiseIntLess xs

increasingSubsequenceLengths : List Int → List Int
increasingSubsequenceLengths nums =
  mapList
    (λ subsequence → pos (listLength subsequence))
    (filterList pairwiseIntLess (allSubseq nums))

longestIncreasingSubsequence-postcond :
  (nums : List Int) →
  (result : Int) →
  longestIncreasingSubsequence-precond nums →
  Set
longestIncreasingSubsequence-postcond nums result h-precond =
  let increasing-lengths = increasingSubsequenceLengths nums
  in
    IsTrue (containsInt result increasing-lengths) ∧
    IsTrue
      (allList
        (λ length → intLessOrEqual length result)
        increasing-lengths)

longestIncreasingSubsequence-spec-satisfied : Set
longestIncreasingSubsequence-spec-satisfied =
  (nums : List Int) →
  (h-precond : longestIncreasingSubsequence-precond nums) →
  longestIncreasingSubsequence-postcond
    nums
    (longestIncreasingSubsequence nums h-precond)
    h-precond
