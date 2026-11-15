-- Statement-only formalization of VERINA corpus artifact verina_advanced_45,
-- catalog title "maxSubarraySum": Kadane's deterministic integer-list program
-- computes a maximum nonempty contiguous-subarray sum, returning zero on the
-- empty list, and is connected to its full contract. This file contains no proof.

{-# OPTIONS --safe #-}

module VerinaAdvanced45 where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Int using (Int; negsuc; pos)
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
intLessOrEqual x y =
  if intLess y x
  then false
  else true

intSuccessor : Int → Int
intSuccessor (pos n) = pos (suc n)
intSuccessor (negsuc zero) = pos zero
intSuccessor (negsuc (suc n)) = negsuc n

intPredecessor : Int → Int
intPredecessor (pos zero) = negsuc zero
intPredecessor (pos (suc n)) = pos n
intPredecessor (negsuc n) = negsuc (suc n)

intAdd : Int → Int → Int
intAdd x (pos zero) = x
intAdd x (pos (suc n)) =
  intSuccessor (intAdd x (pos n))
intAdd x (negsuc zero) = intPredecessor x
intAdd x (negsuc (suc n)) =
  intPredecessor (intAdd x (negsuc n))

intMax : Int → Int → Int
intMax x y =
  if intLess x y
  then y
  else x

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

takeList : {A : Set} → Nat → List A → List A
takeList zero xs = []
takeList (suc n) [] = []
takeList (suc n) (x ∷ xs) =
  x ∷ takeList n xs

dropList : {A : Set} → Nat → List A → List A
dropList zero xs = xs
dropList (suc n) [] = []
dropList (suc n) (_ ∷ xs) = dropList n xs

rangeFrom : Nat → Nat → List Nat
rangeFrom start zero = []
rangeFrom start (suc count) =
  start ∷ rangeFrom (suc start) count

range : Nat → List Nat
range count = rangeFrom zero count

sumList : List Int → Int
sumList [] = pos zero
sumList (x ∷ xs) = intAdd x (sumList xs)

maxSubarraySum-precond : List Int → Set
maxSubarraySum-precond xs = Top

maxSubarraySum-helper : List Int → Int → Int → Int
maxSubarraySum-helper [] curMax globalMax = globalMax
maxSubarraySum-helper (x ∷ rest) curMax globalMax =
  let newCurMax = intMax x (intAdd curMax x)
      newGlobal = intMax globalMax newCurMax
  in maxSubarraySum-helper rest newCurMax newGlobal

maxSubarraySum :
  (xs : List Int) →
  maxSubarraySum-precond xs →
  Int
maxSubarraySum [] h-precond = pos zero
maxSubarraySum (x ∷ rest) h-precond =
  maxSubarraySum-helper rest x x

subarraySums : List Int → List Int
subarraySums xs =
  let n = listLength xs
  in
    flatMapList
      (λ start →
        mapList
          (λ length →
            sumList
              (takeList length (dropList start xs)))
          (rangeFrom
            (suc zero)
            (natSubtract n start)))
      (range (suc n))

maxSubarraySum-postcond :
  (xs : List Int) →
  (result : Int) →
  maxSubarraySum-precond xs →
  Set
maxSubarraySum-postcond [] result h-precond =
  IsTrue (intEqual result (pos zero))
maxSubarraySum-postcond (x ∷ rest) result h-precond =
  IsTrue
    (anyList
      (λ sum → intEqual sum result)
      (subarraySums (x ∷ rest))) ∧
  IsTrue
    (allList
      (λ sum → intLessOrEqual sum result)
      (subarraySums (x ∷ rest)))

maxSubarraySum-spec-satisfied : Set
maxSubarraySum-spec-satisfied =
  (xs : List Int) →
  (h-precond : maxSubarraySum-precond xs) →
  maxSubarraySum-postcond
    xs
    (maxSubarraySum xs h-precond)
    h-precond
