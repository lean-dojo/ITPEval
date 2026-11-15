-- Statement-only formalization of VERINA corpus artifact verina_advanced_46,
-- catalog title "maxSubarraySum": the deterministic integer-list program uses
-- an all-negative shortcut and a recursive maximum-subarray scan, and is
-- connected to its complete correctness contract. This file contains no proof.

{-# OPTIONS --safe #-}

module VerinaAdvanced46 where

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

intToNat : Int → Nat
intToNat (pos n) = n
intToNat (negsuc n) = zero

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

containsInt : Int → List Int → Bool
containsInt sought [] = false
containsInt sought (x ∷ xs) =
  if intEqual sought x
  then true
  else containsInt sought xs

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
maxSubarraySum-precond numbers = Top

isAllNegative : List Int → Bool
isAllNegative [] = true
isAllNegative (x ∷ xs) =
  if intLess x (pos zero)
  then isAllNegative xs
  else false

findMaxProduct : List Int → Int → Int → Int
findMaxProduct [] currMax currSum = currMax
findMaxProduct (x ∷ []) currMax currSum =
  intMax currMax x
findMaxProduct (x ∷ y ∷ rest) currMax currSum =
  let newSum = intMax y (intAdd currSum y)
      newMax = intMax currMax newSum
  in findMaxProduct (y ∷ rest) newMax newSum

handleList : List Int → Nat
handleList [] = zero
handleList (x ∷ rest) =
  if isAllNegative (x ∷ rest)
  then zero
  else
    let initialMax = intMax (pos zero) x
        startSum = intMax (pos zero) x
        result =
          findMaxProduct
            (x ∷ rest)
            initialMax
            startSum
    in intToNat result

maxSubarraySum :
  (numbers : List Int) →
  maxSubarraySum-precond numbers →
  Int
maxSubarraySum numbers h-precond =
  pos (handleList numbers)

subarraySums : List Int → List Int
subarraySums numbers =
  let n = listLength numbers
  in
    flatMapList
      (λ start →
        mapList
          (λ length →
            sumList
              (takeList length (dropList start numbers)))
          (range
            (suc (natSubtract n start))))
      (range (suc n))

maxSubarraySum-postcond :
  (numbers : List Int) →
  (result : Int) →
  maxSubarraySum-precond numbers →
  Set
maxSubarraySum-postcond numbers result h-precond =
  IsTrue (containsInt result (subarraySums numbers)) ∧
  IsTrue
    (allList
      (λ subarraySum → intLessOrEqual subarraySum result)
      (subarraySums numbers))

maxSubarraySum-spec-satisfied : Set
maxSubarraySum-spec-satisfied =
  (numbers : List Int) →
  (h-precond : maxSubarraySum-precond numbers) →
  maxSubarraySum-postcond
    numbers
    (maxSubarraySum numbers h-precond)
    h-precond
