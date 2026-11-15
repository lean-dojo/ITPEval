-- Statement-only formalization of VERINA corpus artifact verina_basic_56,
-- catalog title "copy": a deterministic integer-array program copies a
-- bounded source segment into a destination segment, preserves all other
-- destination entries and its size, and is connected to its correctness
-- contract. This file contains no proof.

{-# OPTIONS --safe #-}

module VerinaBasic56 where

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

copy-precond :
  Array Int →
  Nat →
  Array Int →
  Nat →
  Nat →
  Set
copy-precond src sStart dest dStart len =
  (sStart + len ≤ arraySize src) ∧
  (dStart + len ≤ arraySize dest)

updateSegment :
  Array Int →
  Array Int →
  Nat →
  Nat →
  Nat →
  Array Int
updateSegment r src sStart dStart zero = r
updateSegment r src sStart dStart (suc n) =
  let rNew =
        updateAt
          r
          (dStart + n)
          (indexDefault zeroInt src (sStart + n))
  in updateSegment rNew src sStart dStart n

copy :
  (src : Array Int) →
  (sStart : Nat) →
  (dest : Array Int) →
  (dStart : Nat) →
  (len : Nat) →
  copy-precond src sStart dest dStart len →
  Array Int
copy src sStart dest dStart zero h-precond = dest
copy src sStart dest dStart (suc len) h-precond =
  updateSegment dest src sStart dStart (suc len)

copy-postcond :
  (src : Array Int) →
  (sStart : Nat) →
  (dest : Array Int) →
  (dStart : Nat) →
  (len : Nat) →
  (result : Array Int) →
  copy-precond src sStart dest dStart len →
  Set
copy-postcond src sStart dest dStart len result h-precond =
  (arraySize result ≡ arraySize dest) ∧
  ((i : Nat) →
    i < dStart →
    indexDefault zeroInt result i ≡
      indexDefault zeroInt dest i) ∧
  ((i : Nat) →
    dStart + len ≤ i →
    i < arraySize result →
    indexDefault zeroInt result i ≡
      indexDefault zeroInt dest i) ∧
  ((i : Nat) →
    i < len →
    indexDefault zeroInt result (dStart + i) ≡
      indexDefault zeroInt src (sStart + i))

copy-spec-satisfied : Set
copy-spec-satisfied =
  (src : Array Int) →
  (sStart : Nat) →
  (dest : Array Int) →
  (dStart : Nat) →
  (len : Nat) →
  (h-precond : copy-precond src sStart dest dStart len) →
  copy-postcond
    src
    sStart
    dest
    dStart
    len
    (copy src sStart dest dStart len h-precond)
    h-precond
