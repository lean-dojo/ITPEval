-- Statement-only formalization of VERINA corpus artifact verina_basic_51,
-- catalog title "BinarySearch": a deterministic lower-bound binary search on
-- a nondecreasing integer array returns an insertion index whose prefix is
-- below the key and whose suffix is at least the key. This file contains no proof.

{-# OPTIONS --safe #-}

module VerinaBasic51 where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Int using (Int; negsuc; pos)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using
  (Nat; zero; suc; _+_; div-helper)

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

data IsTrue : Bool → Set where
  true-witness : IsTrue true

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

naturalDiv : Nat → Nat → Nat
naturalDiv numerator zero = zero
naturalDiv numerator (suc denominator) =
  div-helper zero denominator numerator denominator

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

IntLessOrEqual : Int → Int → Set
IntLessOrEqual x y = IsTrue (intLessOrEqual x y)

zeroInt : Int
zeroInt = pos zero

two : Nat
two = suc (suc zero)

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

All : {A : Set} → (A → Set) → List A → Set
All predicate [] = Top
All predicate (x ∷ xs) =
  predicate x ∧ All predicate xs

Pairwise :
  {A : Set} → (A → A → Set) → List A → Set
Pairwise relation [] = Top
Pairwise relation (x ∷ xs) =
  All (relation x) xs ∧ Pairwise relation xs

allList : {A : Set} → (A → Bool) → List A → Bool
allList predicate [] = true
allList predicate (x ∷ xs) =
  if predicate x
  then allList predicate xs
  else false

BinarySearch-precond : Array Int → Int → Set
BinarySearch-precond a key =
  Pairwise IntLessOrEqual a

binarySearchLoopFuel :
  Nat →
  Array Int →
  Int →
  Nat →
  Nat →
  Nat
binarySearchLoopFuel zero a key lo hi = lo
binarySearchLoopFuel (suc fuel) a key lo hi =
  if natLess lo hi
  then
    (let mid = naturalDiv (lo + hi) two
     in
       if intLess (indexDefault zeroInt a mid) key
       then binarySearchLoopFuel fuel a key (suc mid) hi
       else binarySearchLoopFuel fuel a key lo mid)
  else lo

binarySearchLoop :
  Array Int →
  Int →
  Nat →
  Nat →
  Nat
binarySearchLoop a key lo hi =
  binarySearchLoopFuel
    (natSubtract hi lo)
    a
    key
    lo
    hi

BinarySearch :
  (a : Array Int) →
  (key : Int) →
  BinarySearch-precond a key →
  Nat
BinarySearch a key h-precond =
  binarySearchLoop a key zero (arraySize a)

BinarySearch-postcond :
  (a : Array Int) →
  (key : Int) →
  (result : Nat) →
  BinarySearch-precond a key →
  Set
BinarySearch-postcond a key result h-precond =
  (result ≤ arraySize a) ∧
  IsTrue (allList (λ x → intLess x key) (takeList result a)) ∧
  IsTrue
    (allList
      (λ x → intGreaterOrEqual x key)
      (dropList result a))

BinarySearch-spec-satisfied : Set
BinarySearch-spec-satisfied =
  (a : Array Int) →
  (key : Int) →
  (h-precond : BinarySearch-precond a key) →
  BinarySearch-postcond
    a
    key
    (BinarySearch a key h-precond)
    h-precond
