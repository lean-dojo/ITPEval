-- Statement-only formalization of VERINA corpus artifact verina_advanced_57,
-- catalog title "nextGreaterElement": a deterministic monotonic-stack program
-- returns the first greater integer to the right for each requested value.
-- This file contains no proof.

{-# OPTIONS --safe #-}

module VerinaAdvanced57 where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Int using (Int; negsuc; pos)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Maybe using (Maybe; just; nothing)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)

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

boolOr : Bool → Bool → Bool
boolOr true right = true
boolOr false right = right

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

zeroInt : Int
zeroInt = pos zero

minusOne : Int
minusOne = negsuc zero

one : Nat
one = suc zero

listLength : {A : Set} → List A → Nat
listLength [] = zero
listLength (_ ∷ xs) = suc (listLength xs)

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

containsInt : Int → List Int → Bool
containsInt sought [] = false
containsInt sought (x ∷ xs) =
  if intEqual sought x
  then true
  else containsInt sought xs

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

data _∈_ (x : Int) : List Int → Set where
  here : {xs : List Int} → x ∈ (x ∷ xs)
  there : {y : Int} {xs : List Int} → x ∈ xs → x ∈ (y ∷ xs)

NoDuplicates : List Int → Set
NoDuplicates [] = Top
NoDuplicates (x ∷ xs) =
  Not (x ∈ xs) ∧ NoDuplicates xs

nextGreaterElement-precond :
  List Int → List Int → Set
nextGreaterElement-precond nums1 nums2 =
  NoDuplicates nums1 ∧
  NoDuplicates nums2 ∧
  IsTrue (allList (λ x → containsInt x nums2) nums1)

record IntPair : Set where
  constructor pair
  field
    pairFirst : Int
    pairSecond : Int

record StackProcess : Set where
  constructor processed
  field
    remainingStack : List Nat
    updatedMap : List IntPair

open StackProcess

processStack :
  List Int →
  Int →
  List Nat →
  List IntPair →
  StackProcess
processStack nums2 current [] mapping =
  processed [] mapping
processStack nums2 current (top-index ∷ rest) mapping =
  let top-value = nthDefault zeroInt top-index nums2
  in
    if intLess top-value current
    then
      processStack
        nums2
        current
        rest
        (pair top-value current ∷ mapping)
    else processed (top-index ∷ rest) mapping

finalizeStack :
  List Int →
  List Nat →
  List IntPair →
  List IntPair
finalizeStack nums2 stack mapping =
  foldLeft
    (λ accumulator position →
      pair
        (nthDefault zeroInt position nums2)
        minusOne ∷
      accumulator)
    mapping
    stack

mapLoopWithFuel :
  Nat →
  List Int →
  Nat →
  List Nat →
  List IntPair →
  List IntPair
mapLoopWithFuel zero nums2 index stack mapping =
  finalizeStack nums2 stack mapping
mapLoopWithFuel (suc fuel) nums2 index stack mapping =
  let current-value = nthDefault zeroInt index nums2
      stack-result =
        processStack nums2 current-value stack mapping
  in
    mapLoopWithFuel
      fuel
      nums2
      (suc index)
      (index ∷ remainingStack stack-result)
      (updatedMap stack-result)

buildNextGreaterMap : List Int → List IntPair
buildNextGreaterMap nums2 =
  mapLoopWithFuel
    (listLength nums2)
    nums2
    zero
    []
    []

findInMap : Int → List IntPair → Int
findInMap sought [] = minusOne
findInMap sought (pair number next-greater ∷ rest) =
  if intEqual number sought
  then next-greater
  else findInMap sought rest

resultLoopWithFuel :
  Nat →
  List Int →
  Nat →
  List Int →
  List IntPair →
  List Int
resultLoopWithFuel zero nums1 index result mapping =
  reverseList result
resultLoopWithFuel (suc fuel) nums1 index result mapping =
  let value = nthDefault zeroInt index nums1
      next-greater = findInMap value mapping
  in
    resultLoopWithFuel
      fuel
      nums1
      (suc index)
      (next-greater ∷ result)
      mapping

nextGreaterElement :
  (nums1 nums2 : List Int) →
  nextGreaterElement-precond nums1 nums2 →
  List Int
nextGreaterElement nums1 nums2 h-precond =
  let next-greater-map = buildNextGreaterMap nums2
  in
    resultLoopWithFuel
      (listLength nums1)
      nums1
      zero
      []
      next-greater-map

findIndexFrom :
  Int → Nat → List Int → Maybe Nat
findIndexFrom sought index [] = nothing
findIndexFrom sought index (x ∷ xs) =
  if intEqual sought x
  then just index
  else findIndexFrom sought (suc index) xs

findIndex : Int → List Int → Maybe Nat
findIndex sought xs = findIndexFrom sought zero xs

findNat :
  (Nat → Bool) → List Nat → Maybe Nat
findNat predicate [] = nothing
findNat predicate (x ∷ xs) =
  if predicate x
  then just x
  else findNat predicate xs

indexSpecification :
  List Int →
  List Int →
  List Int →
  Nat →
  Bool
indexSpecification nums1 nums2 result i
  with findIndex (nthDefault zeroInt i nums1) nums2
... | nothing = false
... | just index
  with
    findNat
      (λ offset →
        intLess
          (nthDefault zeroInt i nums1)
          (nthDefault
            zeroInt
            (index + offset + one)
            nums2))
      (range
        (natSubtract
          (natSubtract (listLength nums2) index)
          one))
...   | nothing =
  intEqual (nthDefault zeroInt i result) minusOne
...   | just offset =
  intEqual
    (nthDefault zeroInt i result)
    (nthDefault zeroInt (index + offset + one) nums2)

validResultValue : List Int → Int → Bool
validResultValue nums2 value =
  boolOr
    (intEqual value minusOne)
    (containsInt value nums2)

nextGreaterElement-postcond :
  (nums1 nums2 result : List Int) →
  nextGreaterElement-precond nums1 nums2 →
  Set
nextGreaterElement-postcond nums1 nums2 result h-precond =
  (listLength result ≡ listLength nums1) ∧
  IsTrue
    (allList
      (indexSpecification nums1 nums2 result)
      (range (listLength nums1))) ∧
  IsTrue (allList (validResultValue nums2) result)

nextGreaterElement-spec-satisfied : Set
nextGreaterElement-spec-satisfied =
  (nums1 nums2 : List Int) →
  (h-precond : nextGreaterElement-precond nums1 nums2) →
  nextGreaterElement-postcond
    nums1
    nums2
    (nextGreaterElement nums1 nums2 h-precond)
    h-precond
