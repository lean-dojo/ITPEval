-- Statement-only formalization of VERINA corpus artifact verina_basic_87,
-- catalog title "SelectionSort": the deterministic selection-sort array
-- program uses range folds and guarded swaps to return the input integers in
-- nondecreasing order with the same multiset. This file contains no proof.

{-# OPTIONS --safe #-}

module VerinaBasic87 where

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

boolNot : Bool → Bool
boolNot true = false
boolNot false = true

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

natAdd : Nat → Nat → Nat
natAdd zero n = n
natAdd (suc m) n = suc (natAdd m n)

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

IntLessOrEqual : Int → Int → Set
IntLessOrEqual x y = IsTrue (intLessOrEqual x y)

zeroInt : Int
zeroInt = pos zero

Array : Set → Set
Array A = List A

arraySize : {A : Set} → Array A → Nat
arraySize [] = zero
arraySize (_ ∷ xs) = suc (arraySize xs)

arrayToList : {A : Set} → Array A → List A
arrayToList a = a

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

rangeFrom : Nat → Nat → List Nat
rangeFrom start zero = []
rangeFrom start (suc count) =
  start ∷ rangeFrom (suc start) count

range : Nat → List Nat
range count = rangeFrom zero count

foldl :
  {A B : Set} →
  (A → B → A) →
  A →
  List B →
  A
foldl step accumulator [] = accumulator
foldl step accumulator (x ∷ xs) =
  foldl step (step accumulator x) xs

findMinStep :
  Array Int →
  Nat →
  Nat →
  Nat →
  Nat
findMinStep arr start min-index offset =
  let current-index = natAdd start offset
  in
  if intLess
       (indexDefault zeroInt arr current-index)
       (indexDefault zeroInt arr min-index)
  then current-index
  else min-index

findMinIndexInRange :
  Array Int →
  Nat →
  Nat →
  Nat
findMinIndexInRange arr start finish =
  let indices = range (natSubtract finish start)
  in foldl (findMinStep arr start) start indices

swapUnchecked : Array Int → Nat → Nat → Array Int
swapUnchecked a i j =
  let temporary = indexDefault zeroInt a i
      first-update =
        updateAt a i (indexDefault zeroInt a j)
  in updateAt first-update j temporary

swap : Array Int → Nat → Nat → Array Int
swap a i j =
  let in-bounds-and-distinct =
        boolAnd
          (boolAnd
            (natLess i (arraySize a))
            (natLess j (arraySize a)))
          (boolNot (natEqual i j))
  in
  if in-bounds-and-distinct
  then swapUnchecked a i j
  else a

selectionStep : Array Int → Nat → Array Int
selectionStep arr i =
  let min-index =
        findMinIndexInRange arr i (arraySize arr)
  in swap arr i min-index

SelectionSort-precond : Array Int → Set
SelectionSort-precond a = Top

SelectionSort :
  (a : Array Int) →
  SelectionSort-precond a →
  Array Int
SelectionSort a h-precond =
  foldl selectionStep a (range (arraySize a))

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

data Permutation {A : Set} : List A → List A → Set where
  permutationNil :
    Permutation [] []

  permutationSkip :
    {x : A} {xs ys : List A} →
    Permutation xs ys →
    Permutation (x ∷ xs) (x ∷ ys)

  permutationSwap :
    {x y : A} {xs : List A} →
    Permutation (y ∷ x ∷ xs) (x ∷ y ∷ xs)

  permutationTrans :
    {xs ys zs : List A} →
    Permutation xs ys →
    Permutation ys zs →
    Permutation xs zs

SelectionSort-postcond :
  (a : Array Int) →
  (result : Array Int) →
  SelectionSort-precond a →
  Set
SelectionSort-postcond a result h-precond =
  Pairwise IntLessOrEqual (arrayToList result) ∧
  Permutation (arrayToList a) (arrayToList result)

SelectionSort-spec-satisfied : Set
SelectionSort-spec-satisfied =
  (a : Array Int) →
  (h-precond : SelectionSort-precond a) →
  SelectionSort-postcond
    a
    (SelectionSort a h-precond)
    h-precond
