-- Statement-only formalization of VERINA corpus artifact verina_advanced_53,
-- catalog title "minimumRightShifts": a deterministic bounded search returns
-- the minimum cyclic right shifts sorting a distinct integer list, or -1 when
-- no such shift exists. This file contains no proof.

{-# OPTIONS --safe #-}

module VerinaAdvanced53 where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Int using (Int; negsuc; pos)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc)

infixr 2 _∨_
infixr 3 _∧_
infix 4 _≤_ _<_ _∈_

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
  or-left : A → A ∨ B
  or-right : B → A ∨ B

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

chooseSet : Bool → Set → Set → Set
chooseSet true when-true when-false = when-true
chooseSet false when-true when-false = when-false

natLessOrEqual : Nat → Nat → Bool
natLessOrEqual zero _ = true
natLessOrEqual (suc _) zero = false
natLessOrEqual (suc m) (suc n) = natLessOrEqual m n

natSubtract : Nat → Nat → Nat
natSubtract m zero = m
natSubtract zero (suc n) = zero
natSubtract (suc m) (suc n) = natSubtract m n

intLessOrEqual : Int → Int → Bool
intLessOrEqual (pos m) (pos n) = natLessOrEqual m n
intLessOrEqual (pos _) (negsuc _) = false
intLessOrEqual (negsuc _) (pos _) = true
intLessOrEqual (negsuc m) (negsuc n) = natLessOrEqual n m

listLength : {A : Set} → List A → Nat
listLength [] = zero
listLength (_ ∷ xs) = suc (listLength xs)

reverseOnto : {A : Set} → List A → List A → List A
reverseOnto [] accumulator = accumulator
reverseOnto (x ∷ xs) accumulator =
  reverseOnto xs (x ∷ accumulator)

reverseList : {A : Set} → List A → List A
reverseList xs = reverseOnto xs []

rightShiftOnce : {A : Set} → List A → List A
rightShiftOnce xs with reverseList xs
... | [] = []
... | last ∷ reversed-initial =
  last ∷ reverseList reversed-initial

rightShift : {A : Set} → Nat → List A → List A
rightShift zero xs = xs
rightShift (suc shifts) xs =
  rightShift shifts (rightShiftOnce xs)

isSortedAux : List Int → Bool
isSortedAux [] = true
isSortedAux (x ∷ []) = true
isSortedAux (x ∷ y ∷ xs) =
  if intLessOrEqual x y
  then isSortedAux (y ∷ xs)
  else false

data _∈_ (x : Int) : List Int → Set where
  here : {xs : List Int} → x ∈ (x ∷ xs)
  there : {y : Int} {xs : List Int} → x ∈ xs → x ∈ (y ∷ xs)

NoDuplicates : List Int → Set
NoDuplicates [] = Top
NoDuplicates (x ∷ xs) =
  Not (x ∈ xs) ∧ NoDuplicates xs

minimumRightShifts-precond : List Int → Set
minimumRightShifts-precond nums = NoDuplicates nums

checkShiftsWithFuel :
  Nat → Nat → List Int → Int
checkShiftsWithFuel zero shifts current-list = negsuc zero
checkShiftsWithFuel (suc fuel) shifts current-list =
  if isSortedAux current-list
  then pos shifts
  else
    checkShiftsWithFuel
      fuel
      (suc shifts)
      (rightShiftOnce current-list)

checkShifts :
  Nat → Nat → List Int → Int
checkShifts n shifts current-list =
  checkShiftsWithFuel
    (natSubtract n shifts)
    shifts
    current-list

one : Nat
one = suc zero

minimumRightShifts :
  (nums : List Int) →
  minimumRightShifts-precond nums →
  Int
minimumRightShifts nums h-precond =
  let n = listLength nums
  in
    if natLessOrEqual n one
    then pos zero
    else
      if isSortedAux nums
      then pos zero
      else checkShifts n one (rightShiftOnce nums)

All : {A : Set} → (A → Set) → List A → Set
All predicate [] = Top
All predicate (x ∷ xs) =
  predicate x ∧ All predicate xs

Pairwise :
  {A : Set} → (A → A → Set) → List A → Set
Pairwise relation [] = Top
Pairwise relation (x ∷ xs) =
  All (relation x) xs ∧ Pairwise relation xs

IntLessOrEqual : Int → Int → Set
IntLessOrEqual x y = IsTrue (intLessOrEqual x y)

Sorted : List Int → Set
Sorted xs = Pairwise IntLessOrEqual xs

rangeFrom : Nat → Nat → List Nat
rangeFrom start zero = []
rangeFrom start (suc count) =
  start ∷ rangeFrom (suc start) count

range : Nat → List Nat
range n = rangeFrom zero n

intToNat : Int → Nat
intToNat (pos n) = n
intToNat (negsuc n) = zero

IntNonNegative : Int → Set
IntNonNegative (pos n) = Top
IntNonNegative (negsuc n) = Empty

IntLessThanNat : Int → Nat → Set
IntLessThanNat (pos m) n = m < n
IntLessThanNat (negsuc m) n = Top

minimumRightShifts-postcond :
  (nums : List Int) →
  (result : Int) →
  minimumRightShifts-precond nums →
  Set
minimumRightShifts-postcond nums result h-precond =
  let n = listLength nums
      found-minimum =
        IntNonNegative result ∧
        IntLessThanNat result n ∧
        Sorted (rightShift (intToNat result) nums) ∧
        All
          (λ earlier →
            Not (Sorted (rightShift earlier nums)))
          (range (intToNat result))
      no-solution =
        (result ≡ negsuc zero) ∧
        All
          (λ shifts →
            Not (Sorted (rightShift shifts nums)))
          (range n)
  in
    chooseSet
      (natLessOrEqual n one)
      (result ≡ pos zero)
      (found-minimum ∨ no-solution)

minimumRightShifts-spec-satisfied : Set
minimumRightShifts-spec-satisfied =
  (nums : List Int) →
  (h-precond : minimumRightShifts-precond nums) →
  minimumRightShifts-postcond
    nums
    (minimumRightShifts nums h-precond)
    h-precond
