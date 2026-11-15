-- Statement-only formalization of VERINA corpus artifact verina_advanced_80,
-- catalog title "twoSum": a fuel-bounded nested search returns the unique
-- increasing pair of indices whose integer values sum to the target, under
-- the source pair-existence and exact-count precondition. This file contains no proof.

{-# OPTIONS --safe #-}

module VerinaAdvanced80 where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Int using (Int; negsuc; pos)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)

infixr 3 _∧_
infix 4 _≤_ _<_

record _∧_ (A B : Set) : Set where
  constructor both
  field
    first : A
    second : B

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

natLessOrEqual : Nat → Nat → Bool
natLessOrEqual zero n = true
natLessOrEqual (suc m) zero = false
natLessOrEqual (suc m) (suc n) = natLessOrEqual m n

intEqual : Int → Int → Bool
intEqual (pos m) (pos n) = natEqual m n
intEqual (pos _) (negsuc _) = false
intEqual (negsuc _) (pos _) = false
intEqual (negsuc m) (negsuc n) = natEqual m n

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

zeroInt : Int
zeroInt = pos zero

one : Nat
one = suc zero

two : Nat
two = suc one

listLength : {A : Set} → List A → Nat
listLength [] = zero
listLength (_ ∷ xs) = suc (listLength xs)

appendList : {A : Set} → List A → List A → List A
appendList [] ys = ys
appendList (x ∷ xs) ys = x ∷ appendList xs ys

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

anyList : {A : Set} → (A → Bool) → List A → Bool
anyList predicate [] = false
anyList predicate (x ∷ xs) =
  if predicate x
  then true
  else anyList predicate xs

rangeFrom : Nat → Nat → List Nat
rangeFrom start zero = []
rangeFrom start (suc count) =
  start ∷ rangeFrom (suc start) count

range : Nat → List Nat
range count = rangeFrom zero count

indexDefault : {A : Set} → A → List A → Nat → A
indexDefault default [] index = default
indexDefault default (x ∷ xs) zero = x
indexDefault default (x ∷ xs) (suc index) =
  indexDefault default xs index

pairMatches :
  List Int →
  Int →
  Nat →
  Nat →
  Bool
pairMatches nums target i j =
  intEqual
    (intAdd
      (indexDefault zeroInt nums i)
      (indexDefault zeroInt nums j))
    target

pairExists : List Int → Int → Bool
pairExists nums target =
  anyList
    (λ i →
      anyList
        (pairMatches nums target i)
        (range i))
    (range (listLength nums))

matchingPairs : List Int → Int → List Nat
matchingPairs nums target =
  flatMapList
    (λ i →
      filterList
        (pairMatches nums target i)
        (range i))
    (range (listLength nums))

twoSum-precond : List Int → Int → Set
twoSum-precond nums target =
  (two ≤ listLength nums) ∧
  IsTrue (pairExists nums target) ∧
  (listLength (matchingPairs nums target) ≡ one)

findIndices :
  List Int →
  Int →
  Nat →
  Nat →
  Nat →
  List Nat
findIndices nums target i j zero = []
findIndices nums target i j (suc fuel) =
  if natLessOrEqual (listLength nums) i
  then []
  else
    if natLessOrEqual (listLength nums) j
    then findIndices nums target (i + one) (i + two) fuel
    else
      if pairMatches nums target i j
      then i ∷ j ∷ []
      else findIndices nums target i (j + one) fuel

twoSum :
  (nums : List Int) →
  (target : Int) →
  twoSum-precond nums target →
  List Nat
twoSum nums target h-precond =
  findIndices
    nums
    target
    zero
    one
    (listLength nums * listLength nums)

twoSum-postcond :
  (nums : List Int) →
  (target : Int) →
  (result : List Nat) →
  twoSum-precond nums target →
  Set
twoSum-postcond nums target result h-precond =
  (listLength result ≡ two) ∧
  (indexDefault zero result zero < listLength nums) ∧
  (indexDefault zero result one < listLength nums) ∧
  (indexDefault zero result zero <
    indexDefault zero result one) ∧
  (intAdd
    (indexDefault
      zeroInt
      nums
      (indexDefault zero result zero))
    (indexDefault
      zeroInt
      nums
      (indexDefault zero result one)) ≡ target)

twoSum-spec-satisfied : Set
twoSum-spec-satisfied =
  (nums : List Int) →
  (target : Int) →
  (h-precond : twoSum-precond nums target) →
  twoSum-postcond
    nums
    target
    (twoSum nums target h-precond)
    h-precond
