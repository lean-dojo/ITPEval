-- Statement-only formalization of VERINA corpus artifact verina_basic_52,
-- catalog title "BubbleSort": the deterministic bubble-sort array program
-- returns the input integers in nondecreasing order with the same multiset.
-- This file contains no proof.

{-# OPTIONS --safe #-}

module VerinaBasic52 where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Int using (Int; negsuc; pos)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc)

infixr 3 _∧_

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

boolAnd : Bool → Bool → Bool
boolAnd true right = right
boolAnd false right = false

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

intLessOrEqual : Int → Int → Bool
intLessOrEqual (pos m) (pos n) = natLessOrEqual m n
intLessOrEqual (pos _) (negsuc _) = false
intLessOrEqual (negsuc _) (pos _) = true
intLessOrEqual (negsuc m) (negsuc n) =
  natLessOrEqual n m

intGreater : Int → Int → Bool
intGreater x y = intLess y x

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

updateAt : {A : Set} → Array A → Nat → A → Array A
updateAt [] index value = []
updateAt (x ∷ xs) zero value = value ∷ xs
updateAt (x ∷ xs) (suc index) value =
  x ∷ updateAt xs index value

BubbleSort-precond : Array Int → Set
BubbleSort-precond a = Top

swap : Array Int → Nat → Nat → Array Int
swap a i j =
  let temporary = indexDefault zeroInt a i
      first-update =
        updateAt a i (indexDefault zeroInt a j)
  in updateAt first-update j temporary

bubbleInnerSteps :
  Nat →
  Nat →
  Array Int →
  Array Int
bubbleInnerSteps j zero a = a
bubbleInnerSteps j (suc remaining) a =
  let next = suc j
      updated =
        if intGreater
             (indexDefault zeroInt a j)
             (indexDefault zeroInt a next)
        then swap a j next
        else a
  in bubbleInnerSteps next remaining updated

bubbleInner :
  Nat →
  Nat →
  Array Int →
  Array Int
bubbleInner j i a =
  bubbleInnerSteps j (natSubtract i j) a

bubbleOuter : Nat → Array Int → Array Int
bubbleOuter zero a = a
bubbleOuter (suc i) a =
  bubbleOuter i (bubbleInner zero (suc i) a)

BubbleSort :
  (a : Array Int) →
  BubbleSort-precond a →
  Array Int
BubbleSort a h-precond =
  if natEqual (arraySize a) zero
  then a
  else bubbleOuter
         (natSubtract (arraySize a) one)
         a

All : {A : Set} → (A → Set) → List A → Set
All predicate [] = Top
All predicate (x ∷ xs) =
  predicate x ∧ All predicate xs

Pairwise :
  {A : Set} →
  (A → A → Set) →
  List A →
  Set
Pairwise relation [] = Top
Pairwise relation (x ∷ xs) =
  All (relation x) xs ∧ Pairwise relation xs

listIsEmpty : {A : Set} → List A → Bool
listIsEmpty [] = true
listIsEmpty (_ ∷ _) = false

containsInt : List Int → Int → Bool
containsInt [] sought = false
containsInt (x ∷ xs) sought =
  if intEqual x sought
  then true
  else containsInt xs sought

eraseFirstInt : Int → List Int → List Int
eraseFirstInt sought [] = []
eraseFirstInt sought (x ∷ xs) =
  if intEqual x sought
  then xs
  else (x ∷ eraseFirstInt sought xs)

listIsPerm : List Int → List Int → Bool
listIsPerm [] ys = listIsEmpty ys
listIsPerm (x ∷ xs) ys =
  boolAnd
    (containsInt ys x)
    (listIsPerm xs (eraseFirstInt x ys))

BubbleSort-postcond :
  (a : Array Int) →
  (result : Array Int) →
  BubbleSort-precond a →
  Set
BubbleSort-postcond a result h-precond =
  Pairwise IntLessOrEqual result ∧
  IsTrue (listIsPerm result a)

BubbleSort-spec-satisfied : Set
BubbleSort-spec-satisfied =
  (a : Array Int) →
  (h-precond : BubbleSort-precond a) →
  BubbleSort-postcond
    a
    (BubbleSort a h-precond)
    h-precond
