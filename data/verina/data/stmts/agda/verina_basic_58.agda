-- Statement-only formalization of VERINA corpus artifact verina_basic_58,
-- catalog title "double_array_elements": a deterministic integer-array
-- program recursively doubles every original element, preserves the array
-- size, and is connected to its correctness contract. This file contains no proof.

{-# OPTIONS --safe #-}

module VerinaBasic58 where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Int using (Int; negsuc; pos)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc)

infixr 3 _∧_
infix 4 _≤_ _<_

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

_<_ : Nat → Nat → Set
m < n = suc m ≤ n

if_then_else_ : {A : Set} → Bool → A → A → A
if true then when-true else when-false = when-true
if false then when-true else when-false = when-false

natLess : Nat → Nat → Bool
natLess zero zero = false
natLess zero (suc _) = true
natLess (suc _) zero = false
natLess (suc m) (suc n) = natLess m n

natSubtract : Nat → Nat → Nat
natSubtract m zero = m
natSubtract zero (suc n) = zero
natSubtract (suc m) (suc n) = natSubtract m n

intSuccessor : Int → Int
intSuccessor (pos n) = pos (suc n)
intSuccessor (negsuc zero) = pos zero
intSuccessor (negsuc (suc n)) = negsuc n

intPredecessor : Int → Int
intPredecessor (pos zero) = negsuc zero
intPredecessor (pos (suc n)) = pos n
intPredecessor (negsuc n) = negsuc (suc n)

intAdd : Int → Int → Int
intAdd x (pos zero) = x
intAdd x (pos (suc n)) =
  intSuccessor (intAdd x (pos n))
intAdd x (negsuc zero) = intPredecessor x
intAdd x (negsuc (suc n)) =
  intPredecessor (intAdd x (negsuc n))

intDouble : Int → Int
intDouble x = intAdd x x

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

updateAt : {A : Set} → Array A → Nat → A → Array A
updateAt [] index value = []
updateAt (x ∷ xs) zero value = value ∷ xs
updateAt (x ∷ xs) (suc index) value =
  x ∷ updateAt xs index value

double-array-elements-precond : Array Int → Set
double-array-elements-precond s = Top

double-array-elements-aux-fuel :
  Nat →
  Array Int →
  Array Int →
  Nat →
  Array Int
double-array-elements-aux-fuel zero s-old s i = s
double-array-elements-aux-fuel (suc fuel) s-old s i =
  if natLess i (arraySize s)
  then
    (let new-s =
           updateAt
             s
             i
             (intDouble (indexDefault zeroInt s-old i))
     in double-array-elements-aux-fuel
          fuel
          s-old
          new-s
          (suc i))
  else s

double-array-elements-aux :
  Array Int →
  Array Int →
  Nat →
  Array Int
double-array-elements-aux s-old s i =
  double-array-elements-aux-fuel
    (natSubtract (arraySize s) i)
    s-old
    s
    i

double-array-elements :
  (s : Array Int) →
  double-array-elements-precond s →
  Array Int
double-array-elements s h-precond =
  double-array-elements-aux s s zero

double-array-elements-postcond :
  (s : Array Int) →
  (result : Array Int) →
  double-array-elements-precond s →
  Set
double-array-elements-postcond s result h-precond =
  (arraySize result ≡ arraySize s) ∧
  ((i : Nat) →
    i < arraySize s →
    indexDefault zeroInt result i ≡
      intDouble (indexDefault zeroInt s i))

double-array-elements-spec-satisfied : Set
double-array-elements-spec-satisfied =
  (s : Array Int) →
  (h-precond : double-array-elements-precond s) →
  double-array-elements-postcond
    s
    (double-array-elements s h-precond)
    h-precond
