-- Statement-only formalization of VERINA corpus artifact verina_basic_82,
-- catalog title "remove_front": a deterministic integer-array program removes
-- the first element of a nonempty array and is connected to its size-and-shifted-
-- elements correctness contract. This file contains no proof.

{-# OPTIONS --safe #-}

module VerinaBasic82 where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Int using (Int; pos)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)

infixr 3 _∧_
infix 4 _≤_ _<_

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

one : Nat
one = suc zero

zeroInt : Int
zeroInt = pos zero

natSubtract : Nat → Nat → Nat
natSubtract m zero = m
natSubtract zero (suc n) = zero
natSubtract (suc m) (suc n) = natSubtract m n

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

append : {A : Set} → Array A → Array A → Array A
append [] ys = ys
append (x ∷ xs) ys = x ∷ append xs ys

arrayPush : {A : Set} → Array A → A → Array A
arrayPush xs x = append xs (x ∷ [])

arrayMkEmpty : {A : Set} → Nat → Array A
arrayMkEmpty capacity = []

dropArray : {A : Set} → Nat → Array A → Array A
dropArray zero xs = xs
dropArray (suc n) [] = []
dropArray (suc n) (_ ∷ xs) = dropArray n xs

copyFromSuffix : Array Int → Array Int → Array Int
copyFromSuffix [] accumulator = accumulator
copyFromSuffix (x ∷ xs) accumulator =
  copyFromSuffix xs (arrayPush accumulator x)

-- The dropped suffix is exactly the source helper's traversal from index i;
-- each recursive step performs the same push into the accumulator.
copyFrom : Array Int → Nat → Array Int → Array Int
copyFrom a i accumulator =
  copyFromSuffix (dropArray i a) accumulator

remove-front-precond : Array Int → Set
remove-front-precond a = zero < arraySize a

-- The precondition excludes the source program's panic branch. Array capacity
-- is unobservable here, while arrayMkEmpty preserves its initially empty contents.
remove-front :
  (a : Array Int) →
  remove-front-precond a →
  Array Int
remove-front [] ()
remove-front a@(_ ∷ _) h-precond =
  copyFrom
    a
    one
    (arrayMkEmpty (natSubtract (arraySize a) one))

remove-front-postcond :
  (a : Array Int) →
  (result : Array Int) →
  remove-front-precond a →
  Set
remove-front-postcond a result h-precond =
  (zero < arraySize a) ∧
  (arraySize result ≡ natSubtract (arraySize a) one) ∧
  ((i : Nat) →
    i < arraySize result →
    indexDefault zeroInt result i ≡
    indexDefault zeroInt a (i + one))

remove-front-spec-satisfied : Set
remove-front-spec-satisfied =
  (a : Array Int) →
  (h-precond : remove-front-precond a) →
  remove-front-postcond
    a
    (remove-front a h-precond)
    h-precond
