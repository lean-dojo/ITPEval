-- Statement-only formalization of VERINA corpus artifact verina_basic_75,
-- catalog title "minArray": a deterministic scan computes the minimum of a
-- nonempty integer array and is connected to its lower-bound-and-membership
-- correctness contract. This file contains no proof.

{-# OPTIONS --safe #-}

module VerinaBasic75 where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Int using (Int; negsuc; pos)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.Sigma using (Σ)

infixr 3 _∧_
infix 4 _≤_ _<_

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

natLess : Nat → Nat → Bool
natLess zero zero = false
natLess zero (suc _) = true
natLess (suc _) zero = false
natLess (suc m) (suc n) = natLess m n

natLessOrEqual : Nat → Nat → Bool
natLessOrEqual zero _ = true
natLessOrEqual (suc _) zero = false
natLessOrEqual (suc m) (suc n) = natLessOrEqual m n

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

one : Nat
one = suc zero

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

dropArray : {A : Set} → Nat → Array A → Array A
dropArray zero xs = xs
dropArray (suc n) [] = []
dropArray (suc n) (_ ∷ xs) = dropArray n xs

minArray-precond : Array Int → Set
minArray-precond a = zero < arraySize a

minStep : Int → Int → Int
minStep current candidate =
  if intLess candidate current
  then candidate
  else current

minRemaining : Array Int → Int → Int
minRemaining [] current = current
minRemaining (x ∷ xs) current =
  minRemaining xs (minStep current x)

-- Dropping the initial index exposes exactly the suffix traversed by the
-- source helper before its index reaches the array size.
minArray-aux : Array Int → Nat → Int → Int
minArray-aux a index current =
  minRemaining (dropArray index a) current

minArray :
  (a : Array Int) →
  minArray-precond a →
  Int
minArray a h-precond =
  minArray-aux
    a
    one
    (indexDefault zeroInt a zero)

minArray-postcond :
  (a : Array Int) →
  (result : Int) →
  minArray-precond a →
  Set
minArray-postcond a result h-precond =
  ((k : Nat) →
    k < arraySize a →
    IntLessOrEqual
      result
      (indexDefault zeroInt a k)) ∧
  Σ Nat (λ k →
    (k < arraySize a) ∧
    (result ≡ indexDefault zeroInt a k))

minArray-spec-satisfied : Set
minArray-spec-satisfied =
  (a : Array Int) →
  (h-precond : minArray-precond a) →
  minArray-postcond
    a
    (minArray a h-precond)
    h-precond
