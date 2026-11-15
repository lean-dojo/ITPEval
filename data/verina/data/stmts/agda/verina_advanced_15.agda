-- Statement-only formalization of VERINA corpus artifact verina_advanced_15,
-- catalog title "increasingTriplet": a deterministic list program decides
-- whether three entries at increasing indices have strictly increasing values.
-- This file contains no proof.

{-# OPTIONS --safe #-}

module VerinaAdvanced15 where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Int using (Int; negsuc; pos)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Maybe using (Maybe; just; nothing)
open import Agda.Builtin.Nat using (Nat; zero; suc)

infixr 3 _∧_
infixr 5 _&&_ _||_

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

_&&_ : Bool → Bool → Bool
true && other = other
false && other = false

_||_ : Bool → Bool → Bool
true || other = true
false || other = other

natLess : Nat → Nat → Bool
natLess zero zero = false
natLess zero (suc _) = true
natLess (suc _) zero = false
natLess (suc m) (suc n) = natLess m n

natLessOrEqual : Nat → Nat → Bool
natLessOrEqual zero _ = true
natLessOrEqual (suc _) zero = false
natLessOrEqual (suc m) (suc n) = natLessOrEqual m n

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

natGreaterOrEqual : Nat → Nat → Bool
natGreaterOrEqual m n = natLessOrEqual n m

intGreaterOrEqual : Int → Int → Bool
intGreaterOrEqual x y = intLessOrEqual y x

three : Nat
three = suc (suc (suc zero))

listLength : {A : Set} → List A → Nat
listLength [] = zero
listLength (_ ∷ xs) = suc (listLength xs)

IncreasingTriplet-precond : List Int → Set
IncreasingTriplet-precond nums = Top

increasingTripletLoop :
  List Int → Maybe Int → Maybe Int → Bool
increasingTripletLoop [] firstThreshold secondThreshold = false
increasingTripletLoop
  (x ∷ rest)
  nothing
  secondThreshold =
  increasingTripletLoop rest (just x) nothing
increasingTripletLoop (x ∷ rest) (just firstThreshold) nothing =
  if intLessOrEqual x firstThreshold
  then increasingTripletLoop rest (just x) nothing
  else increasingTripletLoop rest (just firstThreshold) (just x)
increasingTripletLoop
  (x ∷ rest)
  (just firstThreshold)
  (just secondThreshold) =
  if intLessOrEqual x firstThreshold
  then increasingTripletLoop rest (just x) (just secondThreshold)
  else
    if intLessOrEqual x secondThreshold
    then increasingTripletLoop rest (just firstThreshold) (just x)
    else true

increasingTriplet :
  (nums : List Int) →
  IncreasingTriplet-precond nums →
  Bool
increasingTriplet nums h-precond =
  if natLess (listLength nums) three
  then false
  else increasingTripletLoop nums nothing nothing

record IndexedInt : Set where
  constructor indexed
  field
    indexedValue : Int
    indexedPosition : Nat

open IndexedInt public

zipIdxFrom : Nat → List Int → List IndexedInt
zipIdxFrom position [] = []
zipIdxFrom position (x ∷ xs) =
  indexed x position ∷ zipIdxFrom (suc position) xs

zipIdx : List Int → List IndexedInt
zipIdx nums = zipIdxFrom zero nums

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

isIncreasingIndexedTriple :
  IndexedInt → IndexedInt → IndexedInt → Bool
isIncreasingIndexedTriple x y z =
  natLess (indexedPosition x) (indexedPosition y) &&
  natLess (indexedPosition y) (indexedPosition z) &&
  intLess (indexedValue x) (indexedValue y) &&
  intLess (indexedValue y) (indexedValue z)

isNotIncreasingIndexedTriple :
  IndexedInt → IndexedInt → IndexedInt → Bool
isNotIncreasingIndexedTriple x y z =
  natGreaterOrEqual (indexedPosition x) (indexedPosition y) ||
  natGreaterOrEqual (indexedPosition y) (indexedPosition z) ||
  intGreaterOrEqual (indexedValue x) (indexedValue y) ||
  intGreaterOrEqual (indexedValue y) (indexedValue z)

hasIncreasingIndexedTriple : List IndexedInt → Bool
hasIncreasingIndexedTriple entries =
  anyList
    (λ x →
      anyList
        (λ y →
          anyList
            (λ z → isIncreasingIndexedTriple x y z)
            entries)
        entries)
    entries

allIndexedTriplesFail : List IndexedInt → Bool
allIndexedTriplesFail entries =
  allList
    (λ x →
      allList
        (λ y →
          allList
            (λ z → isNotIncreasingIndexedTriple x y z)
            entries)
        entries)
    entries

IncreasingTriplet-postcond :
  (nums : List Int) →
  (result : Bool) →
  IncreasingTriplet-precond nums →
  Set
IncreasingTriplet-postcond nums result h-precond =
  let entries = zipIdx nums
  in
    (IsTrue result → IsTrue (hasIncreasingIndexedTriple entries)) ∧
    (Not (IsTrue result) → IsTrue (allIndexedTriplesFail entries))

IncreasingTriplet-spec-satisfied : Set
IncreasingTriplet-spec-satisfied =
  (nums : List Int) →
  (h-precond : IncreasingTriplet-precond nums) →
  IncreasingTriplet-postcond
    nums
    (increasingTriplet nums h-precond)
    h-precond
