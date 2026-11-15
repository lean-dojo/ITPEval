-- Statement-only formalization of VERINA corpus artifact verina_basic_83,
-- catalog title "concat": a deterministic integer-array program concatenates
-- two arrays by writing the first array followed by the second and is connected
-- to its size, prefix, and suffix correctness contract. This file contains no proof.

{-# OPTIONS --safe #-}

module VerinaBasic83 where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Int using (Int; pos)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)

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

Array : Set → Set
Array A = List A

arraySize : {A : Set} → Array A → Nat
arraySize [] = zero
arraySize (_ ∷ xs) = suc (arraySize xs)

zeroInt : Int
zeroInt = pos zero

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

replicate : {A : Set} → Nat → A → Array A
replicate zero value = []
replicate (suc count) value = value ∷ replicate count value

concat-precond : Array Int → Array Int → Set
concat-precond a b = Top

-- Starting at index i, remaining counts exactly the source loop iterations
-- still guarded by i < a.size + b.size.
concatLoop :
  Array Int →
  Array Int →
  Nat →
  Nat →
  Array Int →
  Array Int
concatLoop a b i zero accumulator = accumulator
concatLoop a b i (suc remaining) accumulator =
  let value =
        if natLess i (arraySize a)
        then indexDefault zeroInt a i
        else indexDefault zeroInt b (natSubtract i (arraySize a))
      next = updateAt accumulator i value
  in concatLoop a b (suc i) remaining next

concat :
  (a b : Array Int) →
  concat-precond a b →
  Array Int
concat a b h-precond =
  let n = arraySize a + arraySize b
  in concatLoop a b zero n (replicate n zeroInt)

concat-postcond :
  (a b : Array Int) →
  (result : Array Int) →
  concat-precond a b →
  Set
concat-postcond a b result h-precond =
  (arraySize result ≡ arraySize a + arraySize b) ∧
  ((k : Nat) →
    k < arraySize a →
    indexDefault zeroInt result k ≡
    indexDefault zeroInt a k) ∧
  ((k : Nat) →
    k < arraySize b →
    indexDefault zeroInt result (k + arraySize a) ≡
    indexDefault zeroInt b k)

concat-spec-satisfied : Set
concat-spec-satisfied =
  (a b : Array Int) →
  (h-precond : concat-precond a b) →
  concat-postcond
    a
    b
    (concat a b h-precond)
    h-precond
