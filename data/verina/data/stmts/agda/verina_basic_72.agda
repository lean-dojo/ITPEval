-- Statement-only formalization of VERINA corpus artifact verina_basic_72,
-- catalog title "append": a deterministic integer-array program copies every
-- input entry and appends one integer at the end, and is connected to its
-- index-and-size correctness contract. This file contains no proof.

{-# OPTIONS --safe #-}

module VerinaBasic72 where

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

push : {A : Set} → Array A → A → Array A
push [] x = x ∷ []
push (y ∷ ys) x = y ∷ push ys x

dropArray : {A : Set} → Nat → Array A → Array A
dropArray zero xs = xs
dropArray (suc n) [] = []
dropArray (suc n) (_ ∷ xs) = dropArray n xs

append-precond : Array Int → Int → Set
append-precond a b = Top

copyRemaining :
  Array Int →
  Array Int →
  Array Int
copyRemaining [] accumulator = accumulator
copyRemaining (x ∷ xs) accumulator =
  copyRemaining xs (push accumulator x)

-- Structural recursion over the suffix beginning at i exactly implements the
-- source loop that repeatedly pushes a[i] and increments i until a.size.
copy :
  Array Int →
  Nat →
  Array Int →
  Array Int
copy a i accumulator =
  copyRemaining (dropArray i a) accumulator

append :
  (a : Array Int) →
  (b : Int) →
  append-precond a b →
  Array Int
append a b h-precond =
  let c-initial = copy a zero []
      c-full = push c-initial b
  in c-full

append-postcond :
  (a : Array Int) →
  (b : Int) →
  (result : Array Int) →
  append-precond a b →
  Set
append-postcond a b result h-precond =
  ((i : Nat) →
    i < arraySize a →
    indexDefault zeroInt result i ≡
      indexDefault zeroInt a i) ∧
  (indexDefault zeroInt result (arraySize a) ≡ b) ∧
  (arraySize result ≡ arraySize a + suc zero)

append-spec-satisfied : Set
append-spec-satisfied =
  (a : Array Int) →
  (b : Int) →
  (h-precond : append-precond a b) →
  append-postcond
    a
    b
    (append a b h-precond)
    h-precond
