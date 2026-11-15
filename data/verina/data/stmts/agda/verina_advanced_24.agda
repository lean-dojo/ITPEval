-- Statement-only formalization of VERINA corpus artifact verina_advanced_24,
-- catalog title "lengthOfLIS": a deterministic integer-list program maintains
-- minimal subsequence tails and returns the longest strictly increasing
-- subsequence length characterized by exhaustive subsequence enumeration.
-- This file contains no proof.

{-# OPTIONS --safe #-}

module VerinaAdvanced24 where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Int using (Int; negsuc; pos)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc)

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
intLessOrEqual (pos m) (pos n) = natLessOrEqual m n
intLessOrEqual (pos _) (negsuc _) = false
intLessOrEqual (negsuc _) (pos _) = true
intLessOrEqual (negsuc m) (negsuc n) = natLessOrEqual n m

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

anyList : {A : Set} → (A → Bool) → List A → Bool
anyList predicate [] = false
anyList predicate (x ∷ xs) =
  if predicate x
  then true
  else anyList predicate xs

allList : {A : Set} → (A → Bool) → List A → Bool
allList predicate [] = true
allList predicate (x ∷ xs) =
  if predicate x
  then allList predicate xs
  else false

lengthOfLIS-precond : List Int → Set
lengthOfLIS-precond nums = Top

replaceTail :
  Int → List Int → List Int → List Int
replaceTail x [] accumulator =
  appendList (reverseList accumulator) (x ∷ [])
replaceTail x (y ∷ ys) accumulator =
  if intLessOrEqual x y
  then appendList (reverseList accumulator) (x ∷ ys)
  else replaceTail x ys (y ∷ accumulator)

lisHelper : List Int → Int → List Int
lisHelper dp x = replaceTail x dp []

lengthOfLIS :
  (nums : List Int) →
  lengthOfLIS-precond nums →
  Int
lengthOfLIS nums h-precond =
  pos (listLength (foldLeft lisHelper [] nums))

isStrictlyIncreasing : List Int → Bool
isStrictlyIncreasing [] = true
isStrictlyIncreasing (_ ∷ []) = true
isStrictlyIncreasing (x ∷ y ∷ rest) =
  intLess x y && isStrictlyIncreasing (y ∷ rest)

subsequences : List Int → List (List Int)
subsequences [] = [] ∷ []
subsequences (x ∷ xs) =
  let rest = subsequences xs
  in appendList rest (mapList (λ subsequence → x ∷ subsequence) rest)

increasingSubsequences : List Int → List (List Int)
increasingSubsequences nums =
  filterList isStrictlyIncreasing (subsequences nums)

hasLength : Int → List Int → Bool
hasLength result subsequence =
  intEqual (pos (listLength subsequence)) result

lengthAtMost : Int → List Int → Bool
lengthAtMost result subsequence =
  intLessOrEqual (pos (listLength subsequence)) result

lengthOfLIS-postcond :
  (nums : List Int) →
  (result : Int) →
  lengthOfLIS-precond nums →
  Set
lengthOfLIS-postcond nums result h-precond =
  let allIncreasing = increasingSubsequences nums
  in
    IsTrue (anyList (hasLength result) allIncreasing) ∧
    IsTrue (allList (lengthAtMost result) allIncreasing)

lengthOfLIS-spec-satisfied : Set
lengthOfLIS-spec-satisfied =
  (nums : List Int) →
  (h-precond : lengthOfLIS-precond nums) →
  lengthOfLIS-postcond
    nums
    (lengthOfLIS nums h-precond)
    h-precond
