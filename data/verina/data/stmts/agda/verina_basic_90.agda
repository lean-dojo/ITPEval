-- Statement-only formalization of VERINA corpus artifact verina_basic_90,
-- catalog title "SlopeSearch": a deterministic fuel-bounded search scans a
-- row- and column-sorted integer matrix from its top-right corner and returns
-- a matching index pair or (-1, -1), with its full correctness contract.
-- This file contains no proof.

{-# OPTIONS --safe #-}

module VerinaBasic90 where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Int using (Int; negsuc; pos)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)

infixr 2 _∨_
infixr 3 _∧_
infixr 4 _,_
infixr 5 _×_
infix 4 _≤_ _<_

record Top : Set where
  constructor top

data _∨_ (A B : Set) : Set where
  left : A → A ∨ B
  right : B → A ∨ B

record _∧_ (A B : Set) : Set where
  constructor both
  field
    first-conjunct : A
    second-conjunct : B

record _×_ (A B : Set) : Set where
  constructor _,_
  field
    pairFirst : A
    pairSecond : B

open _×_ public

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

_||_ : Bool → Bool → Bool
true || other = true
false || other = other

notBool : Bool → Bool
notBool true = false
notBool false = true

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

intGreaterOrEqual : Int → Int → Bool
intGreaterOrEqual x y = intLessOrEqual y x

IntLess : Int → Int → Set
IntLess x y = IsTrue (intLess x y)

IntLessOrEqual : Int → Int → Set
IntLessOrEqual x y = IsTrue (intLessOrEqual x y)

zeroInt : Int
zeroInt = pos zero

minusOne : Int
minusOne = negsuc zero

intSuccessor : Int → Int
intSuccessor (pos n) = pos (suc n)
intSuccessor (negsuc zero) = pos zero
intSuccessor (negsuc (suc n)) = negsuc n

intPredecessor : Int → Int
intPredecessor (pos zero) = negsuc zero
intPredecessor (pos (suc n)) = pos n
intPredecessor (negsuc n) = negsuc (suc n)

intToNat : Int → Nat
intToNat (pos n) = n
intToNat (negsuc _) = zero

Array : Set → Set
Array A = List A

Matrix : Set
Matrix = Array (Array Int)

arraySize : {A : Set} → Array A → Nat
arraySize [] = zero
arraySize (_ ∷ xs) = suc (arraySize xs)

indexDefault : {A : Set} → A → Array A → Nat → A
indexDefault default [] index = default
indexDefault default (x ∷ xs) zero = x
indexDefault default (x ∷ xs) (suc index) =
  indexDefault default xs index

mapList : {A B : Set} → (A → B) → List A → List B
mapList f [] = []
mapList f (x ∷ xs) = f x ∷ mapList f xs

rangeFrom : Nat → Nat → List Nat
rangeFrom start zero = []
rangeFrom start (suc count) =
  start ∷ rangeFrom (suc start) count

range : Nat → List Nat
range count = rangeFrom zero count

allList : {A : Set} → (A → Bool) → List A → Bool
allList predicate [] = true
allList predicate (x ∷ xs) =
  if predicate x
  then allList predicate xs
  else false

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

get2d : Matrix → Int → Int → Int
get2d a i j =
  indexDefault
    zeroInt
    (indexDefault [] a (intToNat i))
    (intToNat j)

sameRowSize : Array Int → Array Int → Set
sameRowSize first-row second-row =
  arraySize first-row ≡ arraySize second-row

sortedRow : Array Int → Set
sortedRow row =
  Pairwise IntLessOrEqual row

columnAt : Nat → Matrix → Array Int
columnAt j a =
  mapList
    (λ row → indexDefault zeroInt row j)
    a

sortedColumn : Matrix → Nat → Set
sortedColumn a j =
  Pairwise IntLessOrEqual (columnAt j a)

SlopeSearch-precond : Matrix → Int → Set
SlopeSearch-precond a key =
  let first-row = indexDefault [] a zero
  in
    (zero < arraySize a) ∧
    (zero < arraySize first-row) ∧
    Pairwise sameRowSize a ∧
    All sortedRow a ∧
    All (sortedColumn a) (range (arraySize first-row))

numberOfColumns : Matrix → Nat
numberOfColumns a =
  let rows = arraySize a
  in
    if natLess zero rows
    then arraySize (indexDefault [] a zero)
    else zero

slopeSearchAux :
  Matrix →
  Int →
  Nat →
  Int →
  Int →
  Nat →
  Int × Int
slopeSearchAux a key rows m n zero =
  minusOne , minusOne
slopeSearchAux a key rows m n (suc fuel) =
  if intGreaterOrEqual m (pos rows) || intLess n zeroInt
  then minusOne , minusOne
  else
    let value = get2d a m n
    in
      if intEqual value key
      then m , n
      else
        if intLess value key
        then
          slopeSearchAux
            a
            key
            rows
            (intSuccessor m)
            n
            fuel
        else
          slopeSearchAux
            a
            key
            rows
            m
            (intPredecessor n)
            fuel

SlopeSearch :
  (a : Matrix) →
  (key : Int) →
  SlopeSearch-precond a key →
  Int × Int
SlopeSearch a key h-precond =
  let rows = arraySize a
      cols = numberOfColumns a
      initial-column = pos (natSubtract cols (suc zero))
  in
    slopeSearchAux
      a
      key
      rows
      zeroInt
      initial-column
      (rows + cols)

SlopeSearch-postcond :
  (a : Matrix) →
  (key : Int) →
  (result : Int × Int) →
  SlopeSearch-precond a key →
  Set
SlopeSearch-postcond a key result h-precond =
  let m = pairFirst result
      n = pairSecond result
      rows = arraySize a
      cols = arraySize (indexDefault [] a zero)
  in
    (IntLessOrEqual zeroInt m ∧
     IntLess m (pos rows) ∧
     IntLessOrEqual zeroInt n ∧
     IntLess n (pos cols) ∧
     get2d a m n ≡ key) ∨
    (m ≡ minusOne ∧
     n ≡ minusOne ∧
     IsTrue
       (allList
         (λ row →
           allList
             (λ element → notBool (intEqual element key))
             row)
         a))

SlopeSearch-spec-satisfied : Set
SlopeSearch-spec-satisfied =
  (a : Matrix) →
  (key : Int) →
  (h-precond : SlopeSearch-precond a key) →
  SlopeSearch-postcond
    a
    key
    (SlopeSearch a key h-precond)
    h-precond
