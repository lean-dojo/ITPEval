-- Statement-only formalization of VERINA corpus artifact verina_basic_86,
-- catalog title "rotate": a deterministic integer-array program rotates its
-- entries left by a nonnegative offset using Euclidean modular indexing and is
-- connected to its size-and-index correctness contract. This file contains no proof.

{-# OPTIONS --safe #-}

module VerinaBasic86 where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Int using (Int; negsuc; pos)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc; mod-helper)

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

data IntNonnegative : Int → Set where
  nonnegative : {n : Nat} → IntNonnegative (pos n)

if_then_else_ : {A : Set} → Bool → A → A → A
if true then when-true else when-false = when-true
if false then when-true else when-false = when-false

natEqual : Nat → Nat → Bool
natEqual zero zero = true
natEqual zero (suc _) = false
natEqual (suc _) zero = false
natEqual (suc m) (suc n) = natEqual m n

natLess : Nat → Nat → Bool
natLess zero zero = false
natLess zero (suc _) = true
natLess (suc _) zero = false
natLess (suc m) (suc n) = natLess m n

natSubtract : Nat → Nat → Nat
natSubtract m zero = m
natSubtract zero (suc n) = zero
natSubtract (suc m) (suc n) = natSubtract m n

naturalMod : Nat → Nat → Nat
naturalMod numerator zero = numerator
naturalMod numerator (suc denominator) =
  mod-helper zero denominator numerator denominator

intLess : Int → Int → Bool
intLess (pos m) (pos n) = natLess m n
intLess (pos m) (negsuc n) = false
intLess (negsuc m) (pos n) = true
intLess (negsuc m) (negsuc n) = natLess n m

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

intToNat : Int → Nat
intToNat (pos n) = n
intToNat (negsuc n) = zero

-- This is Lean's integer remainder for a nonnegative natural divisor:
-- division by zero returns the dividend, and a positive divisor gives the
-- unique nonnegative Euclidean remainder.
intRemainderNat : Int → Nat → Int
intRemainderNat x zero = x
intRemainderNat (pos n) divisor@(suc _) =
  pos (naturalMod n divisor)
intRemainderNat (negsuc n) divisor@(suc _)
  with naturalMod (suc n) divisor
... | zero = pos zero
... | remainder@(suc _) =
  pos (natSubtract divisor remainder)

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

-- This exposes exactly the index computation in the source helper, including
-- the negative-remainder adjustment (which is redundant for positive length).
rotationIndex : Nat → Int → Nat → Nat
rotationIndex i offset len =
  let idx = intRemainderNat (intAdd (pos i) offset) len
      adjusted =
        if intLess idx zeroInt
        then intAdd idx (pos len)
        else idx
  in intToNat adjusted

rotate-precond : Array Int → Int → Set
rotate-precond a offset = IntNonnegative offset

rotateAuxSteps :
  Array Int →
  Int →
  Nat →
  Nat →
  Array Int →
  Nat →
  Array Int
rotateAuxSteps a offset i len b zero = b
rotateAuxSteps a offset i len b (suc remaining) =
  let idx = rotationIndex i offset len
      new-b =
        updateAt b i (indexDefault zeroInt a idx)
  in rotateAuxSteps a offset (suc i) len new-b remaining

-- len - i is exactly the number of iterations performed by the source guard
-- i < len, so this fuel encoding preserves rotateAux on every input.
rotateAux :
  Array Int →
  Int →
  Nat →
  Nat →
  Array Int →
  Array Int
rotateAux a offset i len b =
  rotateAuxSteps
    a
    offset
    i
    len
    b
    (natSubtract len i)

rotate :
  (a : Array Int) →
  (offset : Int) →
  rotate-precond a offset →
  Array Int
rotate a offset h-precond =
  let len = arraySize a
      default-val = indexDefault zeroInt a zero
      b0 = replicate len default-val
  in rotateAux a offset zero len b0

rotate-postcond :
  (a : Array Int) →
  (offset : Int) →
  (result : Array Int) →
  rotate-precond a offset →
  Set
rotate-postcond a offset result h-precond =
  (arraySize result ≡ arraySize a) ∧
  ((i : Nat) →
    i < arraySize a →
    indexDefault zeroInt result i ≡
      indexDefault
        zeroInt
        a
        (rotationIndex i offset (arraySize a)))

rotate-spec-satisfied : Set
rotate-spec-satisfied =
  (a : Array Int) →
  (offset : Int) →
  (h-precond : rotate-precond a offset) →
  rotate-postcond
    a
    offset
    (rotate a offset h-precond)
    h-precond
