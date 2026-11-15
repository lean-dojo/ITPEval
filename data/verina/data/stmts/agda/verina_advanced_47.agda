-- Statement-only formalization of VERINA corpus artifact verina_advanced_47,
-- catalog title "mergeIntervals": a deterministic integer-interval program
-- insertion-sorts and merges its input, and is connected to the full coverage,
-- separation, endpoint, and no-spurious-merge contract. This file contains no proof.

{-# OPTIONS --safe #-}

module VerinaAdvanced47 where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Int using (Int; negsuc; pos)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc)

infixr 3 _∧_

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
intLessOrEqual x y =
  if intLess y x
  then false
  else true

intMax : Int → Int → Int
intMax x y =
  if intLess x y
  then y
  else x

record IntPair : Set where
  constructor pair
  field
    pairFirst : Int
    pairSecond : Int

open IntPair public

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

anyList : {A : Set} → (A → Bool) → List A → Bool
anyList predicate [] = false
anyList predicate (x ∷ xs) =
  if predicate x
  then true
  else anyList predicate xs

filterList : {A : Set} → (A → Bool) → List A → List A
filterList predicate [] = []
filterList predicate (x ∷ xs) =
  if predicate x
  then x ∷ filterList predicate xs
  else filterList predicate xs

mergeIntervals-precond : List IntPair → Set
mergeIntervals-precond intervals =
  IsTrue
    (allList
      (λ interval →
        intLessOrEqual
          (pairFirst interval)
          (pairSecond interval))
      intervals)

insertInterval : IntPair → List IntPair → List IntPair
insertInterval interval [] = interval ∷ []
insertInterval interval (current ∷ rest)
  with intLessOrEqual
    (pairFirst interval)
    (pairFirst current)
... | true = interval ∷ (current ∷ rest)
... | false = current ∷ (insertInterval interval rest)

sortIntervals : List IntPair → List IntPair
sortIntervals [] = []
sortIntervals (interval ∷ rest) =
  insertInterval interval (sortIntervals rest)

mergeSorted :
  List IntPair →
  List IntPair →
  List IntPair
mergeSorted [] accumulator = reverseList accumulator
mergeSorted (current ∷ rest) [] =
  mergeSorted rest (current ∷ [])
mergeSorted
  (pair start finish ∷ rest)
  (pair previous-start previous-finish ∷ accumulator-tail) =
    if intLessOrEqual start previous-finish
    then
      mergeSorted
        rest
        (pair
          previous-start
          (intMax previous-finish finish) ∷
        accumulator-tail)
    else
      mergeSorted
        rest
        (pair start finish ∷
        (pair previous-start previous-finish ∷
        accumulator-tail))

mergeIntervals :
  (intervals : List IntPair) →
  mergeIntervals-precond intervals →
  List IntPair
mergeIntervals intervals h-precond =
  mergeSorted (sortIntervals intervals) []

coveredByResult :
  List IntPair →
  List IntPair →
  Bool
coveredByResult intervals result =
  allList
    (λ interval →
      anyList
        (λ result-interval →
          boolAnd
            (intLessOrEqual
              (pairFirst result-interval)
              (pairFirst interval))
            (intLessOrEqual
              (pairSecond interval)
              (pairSecond result-interval)))
        result)
    intervals

noOverlap : List IntPair → Bool
noOverlap [] = true
noOverlap (interval ∷ []) = true
noOverlap
  (pair first-start first-finish ∷
   pair second-start second-finish ∷
   rest) =
    boolAnd
      (intLess first-finish second-start)
      (noOverlap (pair second-start second-finish ∷ rest))

resultBounded :
  List IntPair →
  List IntPair →
  Bool
resultBounded intervals result =
  allList
    (λ result-interval →
      boolAnd
        (anyList
          (λ interval →
            intEqual
              (pairFirst interval)
              (pairFirst result-interval))
          intervals)
        (anyList
          (λ interval →
            intEqual
              (pairSecond interval)
              (pairSecond result-interval))
          intervals))
    result

insideResultInterval : IntPair → IntPair → Bool
insideResultInterval result-interval interval =
  boolAnd
    (intLessOrEqual
      (pairFirst result-interval)
      (pairFirst interval))
    (intLessOrEqual
      (pairSecond interval)
      (pairSecond result-interval))

connectedFromEarlier :
  List IntPair →
  IntPair →
  IntPair →
  Bool
connectedFromEarlier intervals result-interval interval =
  anyList
    (λ earlier →
      boolAnd
        (intLessOrEqual
          (pairFirst result-interval)
          (pairFirst earlier))
        (boolAnd
          (intLessOrEqual
            (pairSecond earlier)
            (pairSecond result-interval))
          (boolAnd
            (intLess
              (pairFirst earlier)
              (pairFirst interval))
            (intLessOrEqual
              (pairFirst interval)
              (pairSecond earlier)))))
    intervals

noSpuriousMerge :
  List IntPair →
  List IntPair →
  Bool
noSpuriousMerge intervals result =
  allList
    (λ result-interval →
      allList
        (λ interval →
          boolOr
            (intEqual
              (pairFirst interval)
              (pairFirst result-interval))
            (connectedFromEarlier
              intervals
              result-interval
              interval))
        (filterList
          (insideResultInterval result-interval)
          intervals))
    result

mergeIntervals-postcond :
  (intervals : List IntPair) →
  (result : List IntPair) →
  mergeIntervals-precond intervals →
  Set
mergeIntervals-postcond intervals result h-precond =
  IsTrue (coveredByResult intervals result) ∧
  IsTrue (noOverlap result) ∧
  IsTrue (resultBounded intervals result) ∧
  IsTrue (noSpuriousMerge intervals result)

mergeIntervals-spec-satisfied : Set
mergeIntervals-spec-satisfied =
  (intervals : List IntPair) →
  (h-precond : mergeIntervals-precond intervals) →
  mergeIntervals-postcond
    intervals
    (mergeIntervals intervals h-precond)
    h-precond
