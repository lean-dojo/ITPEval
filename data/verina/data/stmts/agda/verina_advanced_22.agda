-- Statement-only formalization of VERINA corpus artifact verina_advanced_22,
-- catalog title "isPeakValley": a deterministic integer-list program checks
-- for a nonempty strictly increasing phase followed by a nonempty strictly
-- decreasing phase. This file contains no proof.

{-# OPTIONS --safe #-}

module VerinaAdvanced22 where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Int using (Int; negsuc; pos)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)

infixr 3 _∧_
infixr 5 _&&_

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

one : Nat
one = suc zero

zeroInt : Int
zeroInt = pos zero

listLength : {A : Set} → List A → Nat
listLength [] = zero
listLength (_ ∷ xs) = suc (listLength xs)

rangeFrom : Nat → Nat → List Nat
rangeFrom start zero = []
rangeFrom start (suc count) =
  start ∷ rangeFrom (suc start) count

range : Nat → List Nat
range count = rangeFrom zero count

filterList : {A : Set} → (A → Bool) → List A → List A
filterList predicate [] = []
filterList predicate (x ∷ xs) =
  if predicate x
  then x ∷ filterList predicate xs
  else filterList predicate xs

allList : {A : Set} → (A → Bool) → List A → Bool
allList predicate [] = true
allList predicate (x ∷ xs) =
  if predicate x
  then allList predicate xs
  else false

nthDefault : {A : Set} → A → Nat → List A → A
nthDefault default zero [] = default
nthDefault default zero (x ∷ xs) = x
nthDefault default (suc n) [] = default
nthDefault default (suc n) (_ ∷ xs) =
  nthDefault default n xs

isPeakValley-precond : List Int → Set
isPeakValley-precond lst = Top

isPeakValley-aux : List Int → Bool → Bool → Bool
isPeakValley-aux (x ∷ y ∷ rest) increasing startedDecreasing =
  if intLess x y
  then
    if startedDecreasing
    then false
    else isPeakValley-aux (y ∷ rest) true startedDecreasing
  else
    if intLess y x
    then
      if increasing
      then isPeakValley-aux (y ∷ rest) increasing true
      else false
    else false
isPeakValley-aux _ increasing startedDecreasing =
  increasing && startedDecreasing

isPeakValley :
  (lst : List Int) →
  isPeakValley-precond lst →
  Bool
isPeakValley lst h-precond =
  isPeakValley-aux lst false false

isValidPeak : List Int → Nat → Bool
isValidPeak lst p =
  let len = listLength lst
  in
    natLessOrEqual one p &&
    natLess p (natSubtract len one) &&
    allList
      (λ i →
        intLess
          (nthDefault zeroInt i lst)
          (nthDefault zeroInt (i + one) lst))
      (range p) &&
    allList
      (λ i →
        intLess
          (nthDefault zeroInt (p + i + one) lst)
          (nthDefault zeroInt (p + i) lst))
      (range (natSubtract (natSubtract len one) p))

validPeaks : List Int → List Nat
validPeaks lst =
  filterList (isValidPeak lst) (range (listLength lst))

isPeakValley-postcond :
  (lst : List Int) →
  (result : Bool) →
  isPeakValley-precond lst →
  Set
isPeakValley-postcond lst result h-precond =
  let peaks = validPeaks lst
  in
    (Not (peaks ≡ []) → IsTrue result) ∧
    ((listLength peaks ≡ zero) → Not (IsTrue result))

isPeakValley-spec-satisfied : Set
isPeakValley-spec-satisfied =
  (lst : List Int) →
  (h-precond : isPeakValley-precond lst) →
  isPeakValley-postcond
    lst
    (isPeakValley lst h-precond)
    h-precond
