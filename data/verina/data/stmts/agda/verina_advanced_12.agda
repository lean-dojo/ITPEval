-- Statement-only formalization of VERINA corpus artifact verina_advanced_12,
-- catalog title "firstDuplicate": a deterministic list program returns the
-- first integer whose second occurrence is encountered from left to right,
-- or no value when the input has no duplicates. This file contains no proof.

{-# OPTIONS --safe #-}

module VerinaAdvanced12 where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Int using (Int; negsuc; pos)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Maybe using (Maybe; just; nothing)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)

infixr 3 _∧_
infix 4 _≤_ _<_ _∈_
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

_||_ : Bool → Bool → Bool
true || other = true
false || other = other

natEqual : Nat → Nat → Bool
natEqual zero zero = true
natEqual zero (suc _) = false
natEqual (suc _) zero = false
natEqual (suc m) (suc n) = natEqual m n

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

containsInt : Int → List Int → Bool
containsInt sought [] = false
containsInt sought (x ∷ xs) =
  if intEqual sought x
  then true
  else containsInt sought xs

FirstDuplicate-precond : List Int → Set
FirstDuplicate-precond lst = Top

firstDuplicateHelper : List Int → List Int → Maybe Int
firstDuplicateHelper seen [] = nothing
firstDuplicateHelper seen (x ∷ xs) =
  if containsInt x seen
  then just x
  else firstDuplicateHelper (x ∷ seen) xs

firstDuplicate :
  (lst : List Int) →
  FirstDuplicate-precond lst →
  Maybe Int
firstDuplicate lst h-precond = firstDuplicateHelper [] lst

countInt : Int → List Int → Nat
countInt sought [] = zero
countInt sought (x ∷ xs) =
  if intEqual sought x
  then suc (countInt sought xs)
  else countInt sought xs

dropList : {A : Set} → Nat → List A → List A
dropList zero xs = xs
dropList (suc n) [] = []
dropList (suc n) (_ ∷ xs) = dropList n xs

indexOf : Int → List Int → Nat
indexOf sought [] = zero
indexOf sought (x ∷ xs) =
  if intEqual sought x
  then zero
  else suc (indexOf sought xs)

secondOccurrenceIndex : List Int → Int → Nat
secondOccurrenceIndex lst value =
  let firstIndex = indexOf value lst
  in firstIndex + one +
     indexOf value (dropList (firstIndex + one) lst)

allSecondOccurrencesAfter :
  Int → List Int → List Int → Bool
allSecondOccurrencesAfter duplicate original [] = true
allSecondOccurrencesAfter duplicate original (y ∷ ys) =
  if
    natEqual (countInt y original) one ||
    natLessOrEqual
      (secondOccurrenceIndex original duplicate)
      (secondOccurrenceIndex original y)
  then allSecondOccurrencesAfter duplicate original ys
  else false

data _∈_ (x : Int) : List Int → Set where
  here : {xs : List Int} → x ∈ (x ∷ xs)
  there : {y : Int} {xs : List Int} → x ∈ xs → x ∈ (y ∷ xs)

NoDuplicates : List Int → Set
NoDuplicates [] = Top
NoDuplicates (x ∷ xs) = Not (x ∈ xs) ∧ NoDuplicates xs

FirstDuplicate-postcond :
  (lst : List Int) →
  (result : Maybe Int) →
  FirstDuplicate-precond lst →
  Set
FirstDuplicate-postcond lst nothing h-precond = NoDuplicates lst
FirstDuplicate-postcond lst (just x) h-precond =
  (one < countInt x lst) ∧
  IsTrue (allSecondOccurrencesAfter x lst lst)

FirstDuplicate-spec-satisfied : Set
FirstDuplicate-spec-satisfied =
  (lst : List Int) →
  (h-precond : FirstDuplicate-precond lst) →
  FirstDuplicate-postcond
    lst
    (firstDuplicate lst h-precond)
    h-precond
