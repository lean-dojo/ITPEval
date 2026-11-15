-- Statement-only formalization of VERINA corpus artifact verina_advanced_77,
-- catalog title "trapRainWater": a deterministic two-pointer program computes
-- trapped rainwater from natural-number elevations and is connected to its
-- full precondition and postcondition correctness contract. This file contains no proof.

{-# OPTIONS --safe #-}

module VerinaAdvanced77 where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)

infixr 3 _∧_
infix 4 _≤_

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

if_then_else_ : {A : Set} → Bool → A → A → A
if true then when-true else when-false = when-true
if false then when-true else when-false = when-false

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

natPred : Nat → Nat
natPred zero = zero
natPred (suc n) = n

natMin : Nat → Nat → Nat
natMin m n =
  if natLess m n
  then m
  else n

natMax : Nat → Nat → Nat
natMax m n =
  if natLess m n
  then n
  else m

listLength : {A : Set} → List A → Nat
listLength [] = zero
listLength (_ ∷ xs) = suc (listLength xs)

indexDefault : {A : Set} → A → List A → Nat → A
indexDefault default [] index = default
indexDefault default (x ∷ xs) zero = x
indexDefault default (x ∷ xs) (suc index) =
  indexDefault default xs index

takeList : {A : Set} → Nat → List A → List A
takeList zero xs = []
takeList (suc n) [] = []
takeList (suc n) (x ∷ xs) =
  x ∷ takeList n xs

dropList : {A : Set} → Nat → List A → List A
dropList zero xs = xs
dropList (suc n) [] = []
dropList (suc n) (_ ∷ xs) =
  dropList n xs

rangeFrom : Nat → Nat → List Nat
rangeFrom start zero = []
rangeFrom start (suc count) =
  start ∷ rangeFrom (suc start) count

range : Nat → List Nat
range count = rangeFrom zero count

mapList : {A B : Set} → (A → B) → List A → List B
mapList f [] = []
mapList f (x ∷ xs) =
  f x ∷ mapList f xs

foldLeft : {A B : Set} → (A → B → A) → A → List B → A
foldLeft step accumulator [] = accumulator
foldLeft step accumulator (x ∷ xs) =
  foldLeft step (step accumulator x) xs

trapRainWater-precond : List Nat → Set
trapRainWater-precond height = Top

trapLoopFuel :
  Nat →
  List Nat →
  Nat →
  Nat →
  Nat →
  Nat →
  Nat →
  Nat
trapLoopFuel zero height left right left-max right-max water =
  water
trapLoopFuel
  (suc fuel)
  height
  left
  right
  left-max
  right-max
  water =
    if natLess left right
    then
      (let h-left = indexDefault zero height left
           h-right = indexDefault zero height right
       in
         if natLess h-left h-right
         then
           if natLessOrEqual left-max h-left
           then
             trapLoopFuel
               fuel
               height
               (suc left)
               right
               h-left
               right-max
               water
           else
             trapLoopFuel
               fuel
               height
               (suc left)
               right
               left-max
               right-max
               (water + natSubtract left-max h-left)
         else
           if natLessOrEqual right-max h-right
           then
             trapLoopFuel
               fuel
               height
               left
               (natPred right)
               left-max
               h-right
               water
           else
             trapLoopFuel
               fuel
               height
               left
               (natPred right)
               left-max
               right-max
               (water + natSubtract right-max h-right))
    else water

trapLoop :
  List Nat →
  Nat →
  Nat →
  Nat →
  Nat →
  Nat →
  Nat
trapLoop height left right left-max right-max water =
  trapLoopFuel
    (natSubtract right left)
    height
    left
    right
    left-max
    right-max
    water

trapRainWater :
  (height : List Nat) →
  trapRainWater-precond height →
  Nat
trapRainWater height h-precond =
  trapLoop
    height
    zero
    (natSubtract (listLength height) (suc zero))
    zero
    zero
    zero

waterAtIndex : List Nat → Nat → Nat
waterAtIndex height i =
  let left-max =
        foldLeft
          natMax
          zero
          (takeList (i + suc zero) height)
      right-max =
        foldLeft
          natMax
          zero
          (dropList i height)
  in
    natSubtract
      (natMin left-max right-max)
      (indexDefault zero height i)

totalSpecifiedWater : List Nat → Nat
totalSpecifiedWater height =
  foldLeft
    _+_
    zero
    (mapList
      (waterAtIndex height)
      (range (listLength height)))

trapRainWater-postcond :
  (height : List Nat) →
  (result : Nat) →
  trapRainWater-precond height →
  Set
trapRainWater-postcond height result h-precond =
  let total = totalSpecifiedWater height
  in
    (natSubtract result total ≡ zero) ∧
    (total ≤ result)

trapRainWater-spec-satisfied : Set
trapRainWater-spec-satisfied =
  (height : List Nat) →
  (h-precond : trapRainWater-precond height) →
  trapRainWater-postcond
    height
    (trapRainWater height h-precond)
    h-precond
