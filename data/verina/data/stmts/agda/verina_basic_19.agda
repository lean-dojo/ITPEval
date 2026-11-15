-- Statement-only formalization of VERINA corpus artifact verina_basic_19,
-- catalog title "isSorted": a deterministic integer-array scan returns true
-- exactly when every adjacent pair is nondecreasing and is connected to its
-- correctness contract. This file contains no proof.

{-# OPTIONS --safe #-}

module VerinaBasic19 where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Int using (Int; negsuc; pos)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _-_)

infix 2 _↔_
infix 4 _≤_ _<_
infixr 5 _&&_

record Top : Set where
  constructor top

record _↔_ (A B : Set) : Set where
  constructor iff
  field
    forward : A → B
    backward : B → A

data IsTrue : Bool → Set where
  true-witness : IsTrue true

data _≤_ : Nat → Nat → Set where
  zero≤ : {n : Nat} → zero ≤ n
  suc≤suc : {m n : Nat} → m ≤ n → suc m ≤ suc n

_<_ : Nat → Nat → Set
m < n = suc m ≤ n

_&&_ : Bool → Bool → Bool
true && other = other
false && other = false

natLessOrEqual : Nat → Nat → Bool
natLessOrEqual zero _ = true
natLessOrEqual (suc _) zero = false
natLessOrEqual (suc m) (suc n) = natLessOrEqual m n

intLessOrEqual : Int → Int → Bool
intLessOrEqual (pos m) (pos n) = natLessOrEqual m n
intLessOrEqual (pos _) (negsuc _) = false
intLessOrEqual (negsuc _) (pos _) = true
intLessOrEqual (negsuc m) (negsuc n) = natLessOrEqual n m

IntLessOrEqual : Int → Int → Set
IntLessOrEqual x y = IsTrue (intLessOrEqual x y)

one : Nat
one = suc zero

zeroInt : Int
zeroInt = pos zero

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

isSorted-scan : Array Int → Bool
isSorted-scan [] = true
isSorted-scan (x ∷ []) = true
isSorted-scan (x ∷ y ∷ rest) =
  intLessOrEqual x y && isSorted-scan (y ∷ rest)

isSorted-precond : Array Int → Set
isSorted-precond a = Top

isSorted :
  (a : Array Int) →
  isSorted-precond a →
  Bool
isSorted a h-precond = isSorted-scan a

isSorted-postcond :
  (a : Array Int) →
  (result : Bool) →
  isSorted-precond a →
  Set
isSorted-postcond a result h-precond =
  ((i : Nat) →
    i < (arraySize a - one) →
    IntLessOrEqual
      (indexDefault zeroInt a i)
      (indexDefault zeroInt a (i + one)))
  ↔ IsTrue result

isSorted-spec-satisfied : Set
isSorted-spec-satisfied =
  (a : Array Int) →
  (h-precond : isSorted-precond a) →
  isSorted-postcond
    a
    (isSorted a h-precond)
    h-precond
