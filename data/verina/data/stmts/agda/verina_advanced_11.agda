-- Statement-only formalization of VERINA corpus artifact verina_advanced_11,
-- catalog title "findMajorityElement": a deterministic list program returns
-- the first integer occurring strictly more than half the time, or -1 when no
-- such element exists. This file contains no proof.

{-# OPTIONS --safe #-}

module VerinaAdvanced11 where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Int using (Int; negsuc; pos)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Maybe using (Maybe; just; nothing)
open import Agda.Builtin.Nat using
  (Nat; zero; suc; _+_; div-helper)

infixr 2 _∨_
infixr 3 _∧_
infixr 5 _||_

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

data _∨_ (A B : Set) : Set where
  left : A → A ∨ B
  right : B → A ∨ B

data IsTrue : Bool → Set where
  true-witness : IsTrue true

if_then_else_ : {A : Set} → Bool → A → A → A
if true then when-true else when-false = when-true
if false then when-true else when-false = when-false

_||_ : Bool → Bool → Bool
true || other = true
false || other = other

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

one : Nat
one = suc zero

two : Nat
two = suc one

minusOne : Int
minusOne = negsuc zero

naturalDiv : Nat → Nat → Nat
naturalDiv numerator zero = zero
naturalDiv numerator (suc denominator) =
  div-helper zero denominator numerator denominator

listLength : {A : Set} → List A → Nat
listLength [] = zero
listLength (_ ∷ xs) = suc (listLength xs)

foldLeft : {A B : Set} → (A → B → A) → A → List B → A
foldLeft step accumulator [] = accumulator
foldLeft step accumulator (x ∷ xs) =
  foldLeft step (step accumulator x) xs

countStep : Int → Nat → Int → Nat
countStep sought accumulator x =
  if intEqual x sought
  then accumulator + one
  else accumulator

countOccurrences : Int → List Int → Nat
countOccurrences n lst = foldLeft (countStep n) zero lst

halfLength : List Int → Nat
halfLength lst = naturalDiv (listLength lst) two

findFirstMajority : List Int → List Int → Maybe Int
findFirstMajority original [] = nothing
findFirstMajority original (x ∷ xs) =
  if natLess (halfLength original) (countOccurrences x original)
  then just x
  else findFirstMajority original xs

FindMajorityElement-precond : List Int → Set
FindMajorityElement-precond lst = Top

findMajorityElement :
  (lst : List Int) →
  FindMajorityElement-precond lst →
  Int
findMajorityElement lst h-precond
  with findFirstMajority lst lst
... | just x = x
... | nothing = minusOne

filterInt : Int → List Int → List Int
filterInt sought [] = []
filterInt sought (x ∷ xs) =
  if intEqual x sought
  then x ∷ filterInt sought xs
  else filterInt sought xs

filteredCount : Int → List Int → Nat
filteredCount x lst = listLength (filterInt x lst)

allCountsAtMostHalf : List Int → List Int → Bool
allCountsAtMostHalf original [] = true
allCountsAtMostHalf original (x ∷ xs) =
  if natLessOrEqual (filteredCount x original) (halfLength original)
  then allCountsAtMostHalf original xs
  else false

allCountsAtMostHalfOrResult :
  Int → List Int → List Int → Bool
allCountsAtMostHalfOrResult result original [] = true
allCountsAtMostHalfOrResult result original (x ∷ xs) =
  if
    natLessOrEqual (filteredCount x original) (halfLength original)
      || intEqual x result
  then allCountsAtMostHalfOrResult result original xs
  else false

Majority : List Int → Int → Set
Majority lst result =
  IsTrue (natLess (halfLength lst) (filteredCount result lst)) ∧
  IsTrue (allCountsAtMostHalfOrResult result lst lst)

FindMajorityElement-postcond :
  (lst : List Int) →
  (result : Int) →
  FindMajorityElement-precond lst →
  Set
FindMajorityElement-postcond lst result h-precond =
  ((result ≡ minusOne) →
    (IsTrue (allCountsAtMostHalf lst lst) ∨ Majority lst result)) ∧
  (Not (result ≡ minusOne) → Majority lst result)

FindMajorityElement-spec-satisfied : Set
FindMajorityElement-spec-satisfied =
  (lst : List Int) →
  (h-precond : FindMajorityElement-precond lst) →
  FindMajorityElement-postcond
    lst
    (findMajorityElement lst h-precond)
    h-precond
