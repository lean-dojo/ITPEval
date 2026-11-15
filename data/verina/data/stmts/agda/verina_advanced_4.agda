-- Statement-only formalization of VERINA corpus artifact verina_advanced_4,
-- catalog title "LongestIncreasingSubsequence": a deterministic dynamic-programming
-- program computes a longest strictly increasing integer-array subsequence length
-- and is connected to its exhaustive maximality contract. This file contains no proof.

{-# OPTIONS --safe #-}

module VerinaAdvanced4 where

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
intLessOrEqual (negsuc m) (negsuc n) = natLessOrEqual n m

zeroInt : Int
zeroInt = pos zero

oneInt : Int
oneInt = pos (suc zero)

intSuccessor : Int → Int
intSuccessor (pos n) = pos (suc n)
intSuccessor (negsuc zero) = pos zero
intSuccessor (negsuc (suc n)) = negsuc n

intMax : Int → Int → Int
intMax x y =
  if intLess x y then y else x

Array : Set → Set
Array A = List A

listLength : {A : Set} → List A → Nat
listLength [] = zero
listLength (_ ∷ xs) = suc (listLength xs)

arraySize : {A : Set} → Array A → Nat
arraySize = listLength

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

repeatList : {A : Set} → Nat → A → List A
repeatList zero value = []
repeatList (suc n) value = value ∷ repeatList n value

nthDefault : {A : Set} → A → Nat → List A → A
nthDefault default zero [] = default
nthDefault default zero (x ∷ xs) = x
nthDefault default (suc n) [] = default
nthDefault default (suc n) (_ ∷ xs) =
  nthDefault default n xs

setNth : {A : Set} → Nat → A → List A → List A
setNth zero value [] = []
setNth zero value (_ ∷ xs) = value ∷ xs
setNth (suc n) value [] = []
setNth (suc n) value (x ∷ xs) =
  x ∷ setNth n value xs

rangeFrom : Nat → Nat → List Nat
rangeFrom start zero = []
rangeFrom start (suc count) =
  start ∷ rangeFrom (suc start) count

range : Nat → List Nat
range count = rangeFrom zero count

indicesAfterZero : Nat → List Nat
indicesAfterZero zero = []
indicesAfterZero (suc count) = rangeFrom (suc zero) count

containsInt : Int → List Int → Bool
containsInt sought [] = false
containsInt sought (x ∷ xs) =
  if intEqual sought x
  then true
  else containsInt sought xs

LongestIncreasingSubsequence-precond : Array Int → Set
LongestIncreasingSubsequence-precond a = Top

updateDPEntry :
  Array Int →
  Nat →
  List Int →
  Nat →
  List Int
updateDPEntry a i dp j =
  if (intLess
        (nthDefault zeroInt j a)
        (nthDefault zeroInt i a))
  then
    (let newValue =
           intMax
             (nthDefault zeroInt i dp)
             (intSuccessor (nthDefault zeroInt j dp))
     in setNth i newValue dp)
  else dp

updateDPAtIndex :
  Array Int →
  List Int →
  Nat →
  List Int
updateDPAtIndex a dp i =
  foldLeft (updateDPEntry a i) dp (range i)

buildDP : Array Int → List Int
buildDP a =
  foldLeft
    (updateDPAtIndex a)
    (repeatList (arraySize a) oneInt)
    (indicesAfterZero (arraySize a))

LongestIncreasingSubsequence :
  (a : Array Int) →
  LongestIncreasingSubsequence-precond a →
  Int
LongestIncreasingSubsequence a h-precond with buildDP a
... | [] = zeroInt
... | x ∷ xs = foldLeft intMax zeroInt (x ∷ xs)

allSubseqStep :
  List (List Int) →
  Int →
  List (List Int)
allSubseqStep accumulator x =
  appendList
    accumulator
    (mapList (λ subsequence → x ∷ subsequence) accumulator)

allSubseq : Array Int → List (List Int)
allSubseq a =
  mapList
    reverseList
    (foldLeft allSubseqStep ([] ∷ []) a)

pairwiseIntLess : List Int → Bool
pairwiseIntLess [] = true
pairwiseIntLess (x ∷ xs) =
  allList (intLess x) xs && pairwiseIntLess xs

increasingSubsequenceLengths : Array Int → List Int
increasingSubsequenceLengths a =
  mapList
    (λ subsequence → pos (listLength subsequence))
    (filterList pairwiseIntLess (allSubseq a))

LongestIncreasingSubsequence-postcond :
  (a : Array Int) →
  (result : Int) →
  LongestIncreasingSubsequence-precond a →
  Set
LongestIncreasingSubsequence-postcond a result h-precond =
  let increasing-lengths = increasingSubsequenceLengths a
  in
    IsTrue (containsInt result increasing-lengths) ∧
    IsTrue
      (allList
        (λ length → intLessOrEqual length result)
        increasing-lengths)

LongestIncreasingSubsequence-spec-satisfied : Set
LongestIncreasingSubsequence-spec-satisfied =
  (a : Array Int) →
  (h-precond : LongestIncreasingSubsequence-precond a) →
  LongestIncreasingSubsequence-postcond
    a
    (LongestIncreasingSubsequence a h-precond)
    h-precond
