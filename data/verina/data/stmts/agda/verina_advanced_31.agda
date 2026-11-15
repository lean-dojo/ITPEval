-- Statement-only formalization of VERINA corpus artifact verina_advanced_31,
-- catalog title "longestIncreasingSubseqLength": a deterministic program
-- enumerates integer-list subsequences and returns the maximum length among
-- the strictly increasing ones. This file contains no proof.

{-# OPTIONS --safe #-}

module VerinaAdvanced31 where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Int using (Int; negsuc; pos)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc)

infixr 3 _∧_
infixr 5 _&&_

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

natMax : Nat → Nat → Nat
natMax m n =
  if natLess m n
  then n
  else m

intLess : Int → Int → Bool
intLess (pos m) (pos n) = natLess m n
intLess (pos _) (negsuc _) = false
intLess (negsuc _) (pos _) = true
intLess (negsuc m) (negsuc n) = natLess n m

listLength : {A : Set} → List A → Nat
listLength [] = zero
listLength (_ ∷ xs) = suc (listLength xs)

appendList : {A : Set} → List A → List A → List A
appendList [] ys = ys
appendList (x ∷ xs) ys = x ∷ appendList xs ys

mapList : {A B : Set} → (A → B) → List A → List B
mapList f [] = []
mapList f (x ∷ xs) = f x ∷ mapList f xs

filterList : {A : Set} → (A → Bool) → List A → List A
filterList predicate [] = []
filterList predicate (x ∷ xs) =
  if predicate x
  then x ∷ filterList predicate xs
  else filterList predicate xs

foldLeft : {A B : Set} → (A → B → A) → A → List B → A
foldLeft step accumulator [] = accumulator
foldLeft step accumulator (x ∷ xs) =
  foldLeft step (step accumulator x) xs

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

containsNat : Nat → List Nat → Bool
containsNat sought [] = false
containsNat sought (x ∷ xs) =
  if natEqual sought x
  then true
  else containsNat sought xs

longestIncreasingSubseqLength-precond : List Int → Set
longestIncreasingSubseqLength-precond xs = Top

subsequences : {A : Set} → List A → List (List A)
subsequences [] = [] ∷ []
subsequences (x ∷ xs) =
  let subs = subsequences xs
  in
    appendList
      subs
      (mapList (λ subsequence → x ∷ subsequence) subs)

isStrictlyIncreasing : List Int → Bool
isStrictlyIncreasing [] = true
isStrictlyIncreasing (_ ∷ []) = true
isStrictlyIncreasing (x ∷ y ∷ rest) =
  if intLess x y
  then isStrictlyIncreasing (y ∷ rest)
  else false

maximumLengthStep : Nat → List Int → Nat
maximumLengthStep accumulator subsequence =
  natMax accumulator (listLength subsequence)

longestIncreasingSubseqLength :
  (xs : List Int) →
  longestIncreasingSubseqLength-precond xs →
  Nat
longestIncreasingSubseqLength xs h-precond =
  let subs = subsequences xs
      increasing = filterList isStrictlyIncreasing subs
  in foldLeft maximumLengthStep zero increasing

allSubseqStep :
  {A : Set} →
  List (List A) →
  A →
  List (List A)
allSubseqStep accumulator x =
  appendList
    accumulator
    (mapList (λ subsequence → x ∷ subsequence) accumulator)

allSubseq : {A : Set} → List A → List (List A)
allSubseq xs =
  mapList
    reverseList
    (foldLeft allSubseqStep ([] ∷ []) xs)

pairwiseIntLess : List Int → Bool
pairwiseIntLess [] = true
pairwiseIntLess (x ∷ xs) =
  allList (intLess x) xs && pairwiseIntLess xs

increasingSubsequenceLengths : List Int → List Nat
increasingSubsequenceLengths xs =
  mapList
    listLength
    (filterList pairwiseIntLess (allSubseq xs))

longestIncreasingSubseqLength-postcond :
  (xs : List Int) →
  (result : Nat) →
  longestIncreasingSubseqLength-precond xs →
  Set
longestIncreasingSubseqLength-postcond xs result h-precond =
  let increasing-lengths = increasingSubsequenceLengths xs
  in
    IsTrue (containsNat result increasing-lengths) ∧
    IsTrue
      (allList
        (λ length → natLessOrEqual length result)
        increasing-lengths)

longestIncreasingSubseqLength-spec-satisfied : Set
longestIncreasingSubseqLength-spec-satisfied =
  (xs : List Int) →
  (h-precond : longestIncreasingSubseqLength-precond xs) →
  longestIncreasingSubseqLength-postcond
    xs
    (longestIncreasingSubseqLength xs h-precond)
    h-precond
