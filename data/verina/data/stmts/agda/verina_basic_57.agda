-- Statement-only formalization of VERINA corpus artifact verina_basic_57,
-- catalog title "CountLessThan": a deterministic integer-array scan counts
-- exactly the elements below an integer threshold and is connected to its
-- fold-based correctness contract. This file contains no proof.

{-# OPTIONS --safe #-}

module VerinaBasic57 where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Int using (Int; negsuc; pos)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc)

infixr 3 _∧_

record Top : Set where
  constructor top

record _∧_ (A B : Set) : Set where
  constructor both
  field
    first : A
    second : B

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

intLess : Int → Int → Bool
intLess (pos m) (pos n) = natLess m n
intLess (pos _) (negsuc _) = false
intLess (negsuc _) (pos _) = true
intLess (negsuc m) (negsuc n) = natLess n m

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

foldl :
  {A B : Set} →
  (A → B → A) →
  A →
  List B →
  A
foldl step accumulator [] = accumulator
foldl step accumulator (x ∷ xs) =
  foldl step (step accumulator x) xs

CountLessThan-precond : Array Int → Int → Set
CountLessThan-precond numbers threshold = Top

countLessThan-loop :
  Array Int →
  Int →
  Nat →
  Nat →
  Nat →
  Nat
countLessThan-loop numbers threshold i accumulator zero =
  accumulator
countLessThan-loop numbers threshold i accumulator (suc remaining) =
  let new-accumulator =
        if intLess (indexDefault zeroInt numbers i) threshold
        then suc accumulator
        else accumulator
  in countLessThan-loop
       numbers
       threshold
       (suc i)
       new-accumulator
       remaining

countLessThan : Array Int → Int → Nat
countLessThan numbers threshold =
  countLessThan-loop
    numbers
    threshold
    zero
    zero
    (arraySize numbers)

CountLessThan :
  (numbers : Array Int) →
  (threshold : Int) →
  CountLessThan-precond numbers threshold →
  Nat
CountLessThan numbers threshold h-precond =
  countLessThan numbers threshold

countStep : Int → Nat → Int → Nat
countStep threshold accumulator n =
  if intLess n threshold
  then suc accumulator
  else accumulator

CountLessThan-postcond :
  (numbers : Array Int) →
  (threshold : Int) →
  (result : Nat) →
  CountLessThan-precond numbers threshold →
  Set
CountLessThan-postcond numbers threshold result h-precond =
  let expected = foldl (countStep threshold) zero numbers
  in (natSubtract result expected ≡ zero) ∧
     (natSubtract expected result ≡ zero)

CountLessThan-spec-satisfied : Set
CountLessThan-spec-satisfied =
  (numbers : Array Int) →
  (threshold : Int) →
  (h-precond : CountLessThan-precond numbers threshold) →
  CountLessThan-postcond
    numbers
    threshold
    (CountLessThan numbers threshold h-precond)
    h-precond
