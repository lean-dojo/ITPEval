-- Statement-only formalization of VERINA corpus artifact verina_basic_37,
-- catalog title "findFirstOccurrence": a deterministic early-exit scan of a
-- nondecreasing integer array returns the first target index or negative one
-- and is connected to its full first-occurrence correctness contract. This
-- file contains no proof.

{-# OPTIONS --safe #-}

module VerinaBasic37 where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Int using (Int; negsuc; pos)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc)

infixr 2 _∨_
infixr 3 _∧_
infix 4 _≤_ _<_

record Top : Set where
  constructor top

data Empty : Set where

Not : Set → Set
Not A = A → Empty

data _∨_ (A B : Set) : Set where
  left : A → A ∨ B
  right : B → A ∨ B

record _∧_ (A B : Set) : Set where
  constructor both
  field
    first : A
    second : B

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

boolNot : Bool → Bool
boolNot true = false
boolNot false = true

natEqual : Nat → Nat → Bool
natEqual zero zero = true
natEqual zero (suc _) = false
natEqual (suc _) zero = false
natEqual (suc m) (suc n) = natEqual m n

natLessOrEqual : Nat → Nat → Bool
natLessOrEqual zero _ = true
natLessOrEqual (suc _) zero = false
natLessOrEqual (suc m) (suc n) = natLessOrEqual m n

natLess : Nat → Nat → Bool
natLess m n = boolNot (natLessOrEqual n m)

intEqual : Int → Int → Bool
intEqual (pos m) (pos n) = natEqual m n
intEqual (pos _) (negsuc _) = false
intEqual (negsuc _) (pos _) = false
intEqual (negsuc m) (negsuc n) = natEqual m n

intLessOrEqual : Int → Int → Bool
intLessOrEqual (pos m) (pos n) = natLessOrEqual m n
intLessOrEqual (pos _) (negsuc _) = false
intLessOrEqual (negsuc _) (pos _) = true
intLessOrEqual (negsuc m) (negsuc n) = natLessOrEqual n m

intGreater : Int → Int → Bool
intGreater (pos m) (pos n) = natLess n m
intGreater (pos _) (negsuc _) = true
intGreater (negsuc _) (pos _) = false
intGreater (negsuc m) (negsuc n) = natLess m n

IntLessOrEqual : Int → Int → Set
IntLessOrEqual x y = IsTrue (intLessOrEqual x y)

All : {A : Set} → (A → Set) → List A → Set
All predicate [] = Top
All predicate (x ∷ xs) =
  predicate x ∧ All predicate xs

Pairwise :
  {A : Set} → (A → A → Set) → List A → Set
Pairwise relation [] = Top
Pairwise relation (x ∷ xs) =
  All (relation x) xs ∧ Pairwise relation xs

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

zeroInt : Int
zeroInt = pos zero

negativeOne : Int
negativeOne = negsuc zero

intToNat : Int → Nat
intToNat (pos n) = n
intToNat (negsuc _) = zero

findFirstOccurrence-precond : Array Int → Int → Set
findFirstOccurrence-precond arr target =
  Pairwise IntLessOrEqual arr

findFirstOccurrence-loop : Nat → Array Int → Int → Int
findFirstOccurrence-loop index [] target = negativeOne
findFirstOccurrence-loop index (a ∷ rest) target =
  if intEqual a target
  then pos index
  else
    if intGreater a target
    then negativeOne
    else findFirstOccurrence-loop (suc index) rest target

findFirstOccurrence :
  (arr : Array Int) →
  (target : Int) →
  findFirstOccurrence-precond arr target →
  Int
findFirstOccurrence arr target h-precond =
  findFirstOccurrence-loop zero arr target

findFirstOccurrence-postcond :
  (arr : Array Int) →
  (target : Int) →
  (result : Int) →
  findFirstOccurrence-precond arr target →
  Set
findFirstOccurrence-postcond arr target result h-precond =
  ((result ≡ negativeOne) ∨ IntLessOrEqual zeroInt result) ∧
  (IntLessOrEqual zeroInt result →
    (intToNat result < arraySize arr) ∧
    (indexDefault zeroInt arr (intToNat result) ≡ target) ∧
    ((i : Nat) →
      i < intToNat result →
      Not (indexDefault zeroInt arr i ≡ target))) ∧
  (result ≡ negativeOne →
    (i : Nat) →
    i < arraySize arr →
    Not (indexDefault zeroInt arr i ≡ target))

findFirstOccurrence-spec-satisfied : Set
findFirstOccurrence-spec-satisfied =
  (arr : Array Int) →
  (target : Int) →
  (h-precond : findFirstOccurrence-precond arr target) →
  findFirstOccurrence-postcond
    arr
    target
    (findFirstOccurrence arr target h-precond)
    h-precond
