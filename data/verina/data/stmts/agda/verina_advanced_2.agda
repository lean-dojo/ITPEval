-- Statement-only formalization of VERINA corpus artifact verina_advanced_2,
-- catalog title "LongestCommonSubsequence": a deterministic dynamic-programming
-- program computes the length of a longest common subsequence of two integer arrays.
-- This file contains no proof.

{-# OPTIONS --safe #-}

module VerinaAdvanced2 where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Int using (Int; negsuc; pos)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc)

infixr 3 _∧_
infixr 5 _||_

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

_||_ : Bool → Bool → Bool
true || other = true
false || other = other

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

foldLeft : {A B : Set} → (A → B → A) → A → List B → A
foldLeft step accumulator [] = accumulator
foldLeft step accumulator (x ∷ xs) =
  foldLeft step (step accumulator x) xs

mapList : {A B : Set} → (A → B) → List A → List B
mapList f [] = []
mapList f (x ∷ xs) = f x ∷ mapList f xs

appendList : {A : Set} → List A → List A → List A
appendList [] ys = ys
appendList (x ∷ xs) ys = x ∷ appendList xs ys

filterList : {A : Set} → (A → Bool) → List A → List A
filterList predicate [] = []
filterList predicate (x ∷ xs) =
  if predicate x
  then x ∷ filterList predicate xs
  else filterList predicate xs

reverseOnto : {A : Set} → List A → List A → List A
reverseOnto accumulator [] = accumulator
reverseOnto accumulator (x ∷ xs) =
  reverseOnto (x ∷ accumulator) xs

reverseList : {A : Set} → List A → List A
reverseList xs = reverseOnto [] xs

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

predecessor : Nat → Nat
predecessor zero = zero
predecessor (suc n) = n

Matrix : Set
Matrix = List (List Int)

getCell : Matrix → Nat → Nat → Int
getCell matrix i j =
  nthDefault zeroInt j (nthDefault [] i matrix)

setCell : Nat → Nat → Int → Matrix → Matrix
setCell i j value matrix =
  let row = nthDefault [] i matrix
  in setNth i (setNth j value row) matrix

initialMatrix : Nat → Nat → Matrix
initialMatrix rowCount columnCount =
  repeatList rowCount (repeatList columnCount zeroInt)

updateCell :
  Array Int →
  Array Int →
  Nat →
  Matrix →
  Nat →
  Matrix
updateCell a b i matrix j =
  if natEqual i zero || natEqual j zero
  then matrix
  else
    let iPrev = predecessor i
        jPrev = predecessor j
        aValue = nthDefault zeroInt iPrev a
        bValue = nthDefault zeroInt jPrev b
        newValue =
          if intEqual aValue bValue
          then intSuccessor (getCell matrix iPrev jPrev)
          else
            intMax
              (getCell matrix iPrev j)
              (getCell matrix i jPrev)
    in setCell i j newValue matrix

updateRow :
  Array Int →
  Array Int →
  Nat →
  Matrix →
  Nat →
  Matrix
updateRow a b columnCount matrix i =
  foldLeft
    (updateCell a b i)
    matrix
    (range columnCount)

buildMatrix : Array Int → Array Int → Matrix
buildMatrix a b =
  let rowCount = suc (arraySize a)
      columnCount = suc (arraySize b)
      initial = initialMatrix rowCount columnCount
  in
    foldLeft
      (updateRow a b columnCount)
      initial
      (range rowCount)

LongestCommonSubsequence-precond :
  Array Int → Array Int → Set
LongestCommonSubsequence-precond a b = Top

LongestCommonSubsequence :
  (a : Array Int) →
  (b : Array Int) →
  LongestCommonSubsequence-precond a b →
  Int
LongestCommonSubsequence a b h-precond =
  getCell
    (buildMatrix a b)
    (arraySize a)
    (arraySize b)

allSubseqStep :
  List (List Int) → Int → List (List Int)
allSubseqStep accumulator x =
  appendList
    accumulator
    (mapList (λ subsequence → x ∷ subsequence) accumulator)

allSubseq : Array Int → List (List Int)
allSubseq array =
  mapList
    reverseList
    (foldLeft allSubseqStep ([] ∷ []) array)

listIntEqual : List Int → List Int → Bool
listIntEqual [] [] = true
listIntEqual [] (_ ∷ _) = false
listIntEqual (_ ∷ _) [] = false
listIntEqual (x ∷ xs) (y ∷ ys) =
  if intEqual x y
  then listIntEqual xs ys
  else false

containsIntList : List Int → List (List Int) → Bool
containsIntList sought [] = false
containsIntList sought (x ∷ xs) =
  if listIntEqual sought x
  then true
  else containsIntList sought xs

intLength : List Int → Int
intLength xs = pos (listLength xs)

containsInt : Int → List Int → Bool
containsInt sought [] = false
containsInt sought (x ∷ xs) =
  if intEqual sought x
  then true
  else containsInt sought xs

allAtMost : Int → List Int → Bool
allAtMost bound [] = true
allAtMost bound (x ∷ xs) =
  if intLessOrEqual x bound
  then allAtMost bound xs
  else false

commonSubsequenceLengths :
  Array Int → Array Int → List Int
commonSubsequenceLengths a b =
  let subseqA = allSubseq a
      subseqB = allSubseq b
  in
    mapList
      intLength
      (filterList
        (λ subsequence → containsIntList subsequence subseqB)
        subseqA)

LongestCommonSubsequence-postcond :
  (a : Array Int) →
  (b : Array Int) →
  (result : Int) →
  LongestCommonSubsequence-precond a b →
  Set
LongestCommonSubsequence-postcond a b result h-precond =
  let lengths = commonSubsequenceLengths a b
  in
    IsTrue (containsInt result lengths) ∧
    IsTrue (allAtMost result lengths)

LongestCommonSubsequence-spec-satisfied : Set
LongestCommonSubsequence-spec-satisfied =
  (a : Array Int) →
  (b : Array Int) →
  (h-precond : LongestCommonSubsequence-precond a b) →
  LongestCommonSubsequence-postcond
    a
    b
    (LongestCommonSubsequence a b h-precond)
    h-precond
