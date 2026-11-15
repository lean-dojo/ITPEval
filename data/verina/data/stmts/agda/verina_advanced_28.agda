-- Statement-only formalization of VERINA corpus artifact verina_advanced_28,
-- catalog title "longestConsecutive": a deterministic integer-list program
-- returns the length of the longest consecutive-value streak, under the
-- no-duplicates precondition. This file contains no proof.

{-# OPTIONS --safe #-}

module VerinaAdvanced28 where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Int using (Int; negsuc; pos)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc)

infixr 3 _∧_
infix 4 _∈_

data Empty : Set where

Not : Set → Set
Not A = A → Empty

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

intSuccessor : Int → Int
intSuccessor (pos n) = pos (suc n)
intSuccessor (negsuc zero) = pos zero
intSuccessor (negsuc (suc n)) = negsuc n

intPredecessor : Int → Int
intPredecessor (pos zero) = negsuc zero
intPredecessor (pos (suc n)) = pos n
intPredecessor (negsuc n) = negsuc (suc n)

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

takeList : {A : Set} → Nat → List A → List A
takeList zero xs = []
takeList (suc n) [] = []
takeList (suc n) (x ∷ xs) = x ∷ takeList n xs

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

containsInt : Int → List Int → Bool
containsInt sought [] = false
containsInt sought (x ∷ xs) =
  if intEqual sought x
  then true
  else containsInt sought xs

containsNat : Nat → List Nat → Bool
containsNat sought [] = false
containsNat sought (x ∷ xs) =
  if natEqual sought x
  then true
  else containsNat sought xs

data _∈_ (x : Int) : List Int → Set where
  here : {xs : List Int} → x ∈ (x ∷ xs)
  there : {y : Int} {xs : List Int} → x ∈ xs → x ∈ (y ∷ xs)

NoDuplicates : List Int → Set
NoDuplicates [] = Top
NoDuplicates (x ∷ xs) = Not (x ∈ xs) ∧ NoDuplicates xs

longestConsecutive-precond : List Int → Set
longestConsecutive-precond nums = NoDuplicates nums

insertInt : Int → List Int → List Int
insertInt x set =
  if containsInt x set
  then set
  else (x ∷ set)

buildSet : List Int → List Int
buildSet nums = foldLeft (λ set x → insertInt x set) [] nums

scanConsecutive :
  Nat → List Int → Int → Nat → Nat
scanConsecutive zero set current length = length
scanConsecutive (suc fuel) set current length =
  if containsInt (intSuccessor current) set
  then
    scanConsecutive
      fuel
      set
      (intSuccessor current)
      (suc length)
  else length

longestConsecutiveStep :
  List Int → Nat → Nat → Int → Nat
longestConsecutiveStep set fuel maximum x =
  if notBool (containsInt (intPredecessor x) set)
  then
    natMax
      maximum
      (scanConsecutive fuel set x (suc zero))
  else maximum

longestConsecutive :
  (nums : List Int) →
  longestConsecutive-precond nums →
  Nat
longestConsecutive nums h-precond =
  let set = buildSet nums
      fuel = listLength nums
  in
    foldLeft
      (longestConsecutiveStep set fuel)
      zero
      nums

insertSorted : Int → List Int → List Int
insertSorted x [] = x ∷ []
insertSorted x (y ∷ ys) =
  if intLessOrEqual x y
  then (x ∷ y ∷ ys)
  else (y ∷ insertSorted x ys)

sortInts : List Int → List Int
sortInts [] = []
sortInts (x ∷ xs) = insertSorted x (sortInts xs)

consecutiveFrom : Int → List Int → Bool
consecutiveFrom expected [] = true
consecutiveFrom expected (x ∷ xs) =
  if intEqual x expected
  then consecutiveFrom (intSuccessor expected) xs
  else false

isConsecutive : List Int → Bool
isConsecutive [] = true
isConsecutive (x ∷ xs) =
  consecutiveFrom (intSuccessor x) xs

slice : {A : Set} → Nat → Nat → List A → List A
slice start length xs =
  takeList length (dropList start xs)

allSortedSlices : List Int → List (List Int)
allSortedSlices nums =
  let sorted-nums = sortInts nums
      n = listLength nums
  in
    flatMapList
      (λ start →
        mapList
          (λ length → slice start length sorted-nums)
          (range (suc (natSubtract n start))))
      (range n)

consecutiveSublistLengths : List Int → List Nat
consecutiveSublistLengths nums =
  mapList
    listLength
    (filterList isConsecutive (allSortedSlices nums))

longestConsecutive-postcond :
  (nums : List Int) →
  (result : Nat) →
  longestConsecutive-precond nums →
  Set
longestConsecutive-postcond nums result h-precond =
  let consecutive-lengths = consecutiveSublistLengths nums
  in
    (nums ≡ [] → result ≡ zero) ∧
    (Not (nums ≡ []) →
      IsTrue (containsNat result consecutive-lengths) ∧
      IsTrue
        (allList
          (λ length → natLessOrEqual length result)
          consecutive-lengths))

longestConsecutive-spec-satisfied : Set
longestConsecutive-spec-satisfied =
  (nums : List Int) →
  (h-precond : longestConsecutive-precond nums) →
  longestConsecutive-postcond
    nums
    (longestConsecutive nums h-precond)
    h-precond
