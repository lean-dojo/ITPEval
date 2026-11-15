-- Statement-only formalization of VERINA corpus artifact verina_advanced_33,
-- catalog title "longestIncreasingSubsequence": an exhaustive include-or-skip
-- program computes the longest strictly increasing integer subsequence length
-- and is connected to its maximality contract. This file contains no proof.

{-# OPTIONS --safe #-}

module VerinaAdvanced33 where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Int using (Int; negsuc; pos)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Maybe using (Maybe; just; nothing)
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

natGreater : Nat → Nat → Bool
natGreater m n = natLess n m

max2 : Nat → Nat → Nat
max2 a b =
  if natGreater a b
  then a
  else b

intLess : Int → Int → Bool
intLess (pos m) (pos n) = natLess m n
intLess (pos _) (negsuc _) = false
intLess (negsuc _) (pos _) = true
intLess (negsuc m) (negsuc n) = natLess n m

one : Nat
one = suc zero

listLength : {A : Set} → List A → Nat
listLength [] = zero
listLength (_ ∷ xs) = one + listLength xs

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

containsNat : Nat → List Nat → Bool
containsNat sought [] = false
containsNat sought (x ∷ xs) =
  if natEqual sought x
  then true
  else containsNat sought xs

longestIncreasingSubsequence-precond : List Int → Set
longestIncreasingSubsequence-precond nums = Top

longestIncreasingSubsequence-helper :
  List Int →
  Maybe Int →
  Nat
longestIncreasingSubsequence-helper [] previous = zero
longestIncreasingSubsequence-helper (head ∷ tail) nothing =
  let can-take = true
      with-take =
        if can-take
        then one + longestIncreasingSubsequence-helper tail (just head)
        else zero
      without-take =
        longestIncreasingSubsequence-helper tail nothing
  in max2 with-take without-take
longestIncreasingSubsequence-helper (head ∷ tail) (just previous) =
  let can-take =
        if intLess previous head
        then true
        else false
      with-take =
        if can-take
        then one + longestIncreasingSubsequence-helper tail (just head)
        else zero
      without-take =
        longestIncreasingSubsequence-helper tail (just previous)
  in max2 with-take without-take

longestIncreasingSubsequence :
  (nums : List Int) →
  longestIncreasingSubsequence-precond nums →
  Nat
longestIncreasingSubsequence nums h-precond =
  longestIncreasingSubsequence-helper nums nothing

allSubseqStep :
  {A : Set} →
  List (List A) →
  A →
  List (List A)
allSubseqStep accumulator x =
  appendList
    accumulator
    (mapList (λ subsequence → x ∷ subsequence) accumulator)

allSubseq : {A : Set} → List A → List (List A)
allSubseq xs =
  mapList
    reverseList
    (foldLeft allSubseqStep ([] ∷ []) xs)

pairwiseIntLess : List Int → Bool
pairwiseIntLess [] = true
pairwiseIntLess (x ∷ xs) =
  allList (intLess x) xs && pairwiseIntLess xs

increasingSubsequenceLengths : List Int → List Nat
increasingSubsequenceLengths nums =
  mapList
    listLength
    (filterList pairwiseIntLess (allSubseq nums))

longestIncreasingSubsequence-postcond :
  (nums : List Int) →
  (result : Nat) →
  longestIncreasingSubsequence-precond nums →
  Set
longestIncreasingSubsequence-postcond nums result h-precond =
  let increasing-lengths = increasingSubsequenceLengths nums
  in
    IsTrue (containsNat result increasing-lengths) ∧
    IsTrue
      (allList
        (λ length → natLessOrEqual length result)
        increasing-lengths)

longestIncreasingSubsequence-spec-satisfied : Set
longestIncreasingSubsequence-spec-satisfied =
  (nums : List Int) →
  (h-precond : longestIncreasingSubsequence-precond nums) →
  longestIncreasingSubsequence-postcond
    nums
    (longestIncreasingSubsequence nums h-precond)
    h-precond
