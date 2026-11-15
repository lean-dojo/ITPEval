-- Statement-only formalization of VERINA corpus artifact verina_basic_105,
-- catalog title "arrayProduct": a deterministic integer-array program computes
-- the elementwise product of equal-length arrays and is connected to its
-- size-and-indexed-value correctness contract. This file contains no proof.

{-# OPTIONS --safe #-}

module VerinaBasic105 where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Int using (Int; negsuc; pos)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)

infix 4 _≤_ _<_
infixl 7 _*z_
infixr 3 _∧_

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

negative : Nat → Int
negative zero = pos zero
negative (suc n) = negsuc n

_*z_ : Int → Int → Int
pos m *z pos n = pos (m * n)
pos m *z negsuc n = negative (m * suc n)
negsuc m *z pos n = negative (suc m * n)
negsuc m *z negsuc n = pos (suc m * suc n)

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

replicate : {A : Set} → Nat → A → Array A
replicate zero value = []
replicate (suc n) value = value ∷ replicate n value

natSubtract : Nat → Nat → Nat
natSubtract m zero = m
natSubtract zero (suc n) = zero
natSubtract (suc m) (suc n) = natSubtract m n

loopSteps :
  Array Int →
  Array Int →
  Nat →
  Nat →
  Array Int →
  Array Int
loopSteps a b zero i c = c
loopSteps a b (suc remaining) i c =
  let a-val = indexDefault zeroInt a i
      b-val = indexDefault zeroInt b i
      new-c = updateAt c i (a-val *z b-val)
  in loopSteps a b remaining (suc i) new-c

loop :
  Array Int →
  Array Int →
  Nat →
  Nat →
  Array Int →
  Array Int
loop a b len i c =
  loopSteps a b (natSubtract len i) i c

arrayProduct-precond : Array Int → Array Int → Set
arrayProduct-precond a b =
  arraySize a ≡ arraySize b

arrayProduct :
  (a : Array Int) →
  (b : Array Int) →
  arrayProduct-precond a b →
  Array Int
arrayProduct a b h-precond =
  let len = arraySize a
      c = replicate len zeroInt
  in loop a b len zero c

arrayProduct-postcond :
  (a : Array Int) →
  (b : Array Int) →
  (result : Array Int) →
  arrayProduct-precond a b →
  Set
arrayProduct-postcond a b result h-precond =
  (arraySize result ≡ arraySize a) ∧
  ((i : Nat) →
    i < arraySize a →
    (indexDefault zeroInt a i *z indexDefault zeroInt b i) ≡
      indexDefault zeroInt result i)

arrayProduct-spec-satisfied : Set
arrayProduct-spec-satisfied =
  (a : Array Int) →
  (b : Array Int) →
  (h-precond : arrayProduct-precond a b) →
  arrayProduct-postcond
    a
    b
    (arrayProduct a b h-precond)
    h-precond
