-- Statement-only formalization of VERINA corpus artifact verina_basic_40,
-- catalog title "secondSmallest": a deterministic integer-array scan returns
-- the second-smallest distinct value and is connected to its distinctness,
-- membership, and ordering correctness contract. This file contains no proof.

{-# OPTIONS --safe #-}

module VerinaBasic40 where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Int using (Int; negsuc; pos)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Maybe using (Maybe; just; nothing)
open import Agda.Builtin.Nat using (Nat; zero; suc)

infixr 3 _∧_
infix 4 _≤_ _<_ _≠_

data Empty : Set where

Not : Set → Set
Not A = A → Empty

_≠_ : {A : Set} → A → A → Set
x ≠ y = Not (x ≡ y)

record _∧_ (A B : Set) : Set where
  constructor both
  field
    first : A
    second : B

record Exists {A : Set} (predicate : A → Set) : Set where
  constructor witness
  field
    value : A
    evidence : predicate value

data IsTrue : Bool → Set where
  true-witness : IsTrue true

data _≤_ : Nat → Nat → Set where
  zero≤ : {n : Nat} → zero ≤ n
  suc≤suc : {m n : Nat} → m ≤ n → suc m ≤ suc n

_<_ : Nat → Nat → Set
m < n = suc m ≤ n

if_then_else_ : {A : Set} → Bool → A → A → A
if true then when-true else when-false = when-true
if false then when-true else when-false = when-false

andBool : Bool → Bool → Bool
andBool true right = right
andBool false right = false

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

IntLess : Int → Int → Set
IntLess x y = IsTrue (intLess x y)

IntLessOrEqual : Int → Int → Set
IntLessOrEqual x y = IsTrue (intLessOrEqual x y)

zeroInt : Int
zeroInt = pos zero

one : Nat
one = suc zero

Array : Set → Set
Array A = List A

arraySize : {A : Set} → Array A → Nat
arraySize [] = zero
arraySize (_ ∷ xs) = suc (arraySize xs)

indexDefault : {A : Set} → A → Array A → Nat → A
indexDefault default [] index = default
indexDefault default (x ∷ xs) zero = x
indexDefault default (x ∷ xs) (suc index) =
  indexDefault default xs index

secondSmallest-precond : Array Int → Set
secondSmallest-precond s =
  (one < arraySize s) ∧
  Exists
    (λ i →
      (i < arraySize s) ∧
      Exists
        (λ j →
          (j < arraySize s) ∧
          (indexDefault zeroInt s i ≠
            indexDefault zeroInt s j)))

secondSmallestAuxSteps :
  Nat →
  Array Int →
  Nat →
  Nat →
  Maybe Nat →
  Int
secondSmallestAuxSteps zero s i minIdx nothing =
  zeroInt
secondSmallestAuxSteps zero s i minIdx (just secondIdx) =
  indexDefault zeroInt s secondIdx
secondSmallestAuxSteps (suc remaining) s i minIdx nothing =
  let x = indexDefault zeroInt s i
      minimum = indexDefault zeroInt s minIdx
  in
    if intLess x minimum
    then
      secondSmallestAuxSteps
        remaining s (suc i) i (just minIdx)
    else
      if intLess minimum x
      then
        secondSmallestAuxSteps
          remaining s (suc i) minIdx (just i)
      else
        secondSmallestAuxSteps
          remaining s (suc i) minIdx nothing
secondSmallestAuxSteps
  (suc remaining) s i minIdx (just secondIdx) =
  let x = indexDefault zeroInt s i
      minimum = indexDefault zeroInt s minIdx
      secondMinimum = indexDefault zeroInt s secondIdx
  in
    if intLess x minimum
    then
      secondSmallestAuxSteps
        remaining s (suc i) i (just minIdx)
    else
      if andBool
           (intLess x secondMinimum)
           (intLess minimum x)
      then
        secondSmallestAuxSteps
          remaining s (suc i) minIdx (just i)
      else
        secondSmallestAuxSteps
          remaining s (suc i) minIdx (just secondIdx)

secondSmallestAux :
  Array Int →
  Nat →
  Nat →
  Maybe Nat →
  Int
secondSmallestAux s i minIdx secondIdx =
  secondSmallestAuxSteps
    (natSubtract (arraySize s) i)
    s
    i
    minIdx
    secondIdx

secondSmallest :
  (s : Array Int) →
  secondSmallest-precond s →
  Int
secondSmallest s h-precond =
  secondSmallestAux s one zero nothing

secondSmallest-postcond :
  (s : Array Int) →
  (result : Int) →
  secondSmallest-precond s →
  Set
secondSmallest-postcond s result h-precond =
  Exists
    (λ i →
      (i < arraySize s) ∧
      (indexDefault zeroInt s i ≡ result)) ∧
  Exists
    (λ j →
      (j < arraySize s) ∧
      IntLess (indexDefault zeroInt s j) result ∧
      ((k : Nat) →
        k < arraySize s →
        indexDefault zeroInt s k ≠
          indexDefault zeroInt s j →
        IntLessOrEqual result
          (indexDefault zeroInt s k)))

secondSmallest-spec-satisfied : Set
secondSmallest-spec-satisfied =
  (s : Array Int) →
  (h-precond : secondSmallest-precond s) →
  secondSmallest-postcond
    s
    (secondSmallest s h-precond)
    h-precond
