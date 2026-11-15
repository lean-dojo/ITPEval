-- Statement-only formalization of VERINA corpus artifact verina_basic_106,
-- catalog title "arraySum": a deterministic integer-array program computes
-- the elementwise sum of equal-length arrays and is connected to its
-- size-and-indexed-value correctness contract. This file contains no proof.

{-# OPTIONS --safe #-}

module VerinaBasic106 where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Int using (Int; negsuc; pos)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc)

infix 4 _≤_ _<_
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
      new-c = updateAt c i (intAdd a-val b-val)
  in loopSteps a b remaining (suc i) new-c

loop :
  Array Int →
  Array Int →
  Nat →
  Nat →
  Array Int →
  Array Int
loop a b n i c =
  loopSteps a b (natSubtract n i) i c

arraySum-precond : Array Int → Array Int → Set
arraySum-precond a b =
  arraySize a ≡ arraySize b

arraySum :
  (a : Array Int) →
  (b : Array Int) →
  arraySum-precond a b →
  Array Int
arraySum a b h-precond =
  let n = arraySize a
      c = replicate n zeroInt
  in loop a b n zero c

arraySum-postcond :
  (a : Array Int) →
  (b : Array Int) →
  (result : Array Int) →
  arraySum-precond a b →
  Set
arraySum-postcond a b result h-precond =
  (arraySize result ≡ arraySize a) ∧
  ((i : Nat) →
    i < arraySize a →
    intAdd
      (indexDefault zeroInt a i)
      (indexDefault zeroInt b i) ≡
      indexDefault zeroInt result i)

arraySum-spec-satisfied : Set
arraySum-spec-satisfied =
  (a : Array Int) →
  (b : Array Int) →
  (h-precond : arraySum-precond a b) →
  arraySum-postcond
    a
    b
    (arraySum a b h-precond)
    h-precond
