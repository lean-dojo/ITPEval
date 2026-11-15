-- Statement-only formalization of VERINA corpus artifact verina_basic_64,
-- catalog title "insert": a deterministic character-array program inserts
-- the first p characters of nl into the first l characters of oline at atPos
-- and is connected to its size and pointwise correctness contract. This file
-- contains no proof.

{-# OPTIONS --safe #-}

module VerinaBasic64 where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Char using (Char; primNatToChar)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)

infixr 3 _∧_
infix 4 _≤_

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

natSubtract : Nat → Nat → Nat
natSubtract m zero = m
natSubtract zero (suc n) = zero
natSubtract (suc m) (suc n) = natSubtract m n

Array : Set → Set
Array A = List A

arraySize : {A : Set} → Array A → Nat
arraySize [] = zero
arraySize (_ ∷ xs) = suc (arraySize xs)

nullChar : Char
nullChar = primNatToChar zero

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

rangeFrom : Nat → Nat → List Nat
rangeFrom start zero = []
rangeFrom start (suc count) =
  start ∷ rangeFrom (suc start) count

range : Nat → List Nat
range count = rangeFrom zero count

foldl :
  {A B : Set} →
  (A → B → A) →
  A →
  List B →
  A
foldl step accumulator [] = accumulator
foldl step accumulator (x ∷ xs) =
  foldl step (step accumulator x) xs

All : {A : Set} → (A → Set) → List A → Set
All predicate [] = Top
All predicate (x ∷ xs) =
  predicate x ∧ All predicate xs

insert-precond :
  Array Char →
  Nat →
  Array Char →
  Nat →
  Nat →
  Set
insert-precond oline l nl p atPos =
  (l ≤ arraySize oline) ∧
  (p ≤ arraySize nl) ∧
  (atPos ≤ l)

copyPrefixStep :
  Array Char →
  Nat →
  Array Char →
  Nat →
  Array Char
copyPrefixStep oline atPos accumulator i =
  if natLess i atPos
  then
    updateAt
      accumulator
      i
      (indexDefault nullChar oline i)
  else accumulator

insertNewStep :
  Array Char →
  Nat →
  Array Char →
  Nat →
  Array Char
insertNewStep nl atPos accumulator i =
  updateAt
    accumulator
    (atPos + i)
    (indexDefault nullChar nl i)

copySuffixStep :
  Array Char →
  Nat →
  Nat →
  Array Char →
  Nat →
  Array Char
copySuffixStep oline atPos p accumulator i =
  if natLessOrEqual atPos i
  then
    updateAt
      accumulator
      (i + p)
      (indexDefault nullChar oline i)
  else accumulator

insert :
  (oline : Array Char) →
  (l : Nat) →
  (nl : Array Char) →
  (p : Nat) →
  (atPos : Nat) →
  insert-precond oline l nl p atPos →
  Array Char
insert oline l nl p atPos h-precond =
  let initial-result = replicate (l + p) ' '
      prefix-result =
        foldl
          (copyPrefixStep oline atPos)
          initial-result
          (range l)
      inserted-result =
        foldl
          (insertNewStep nl atPos)
          prefix-result
          (range p)
      final-result =
        foldl
          (copySuffixStep oline atPos p)
          inserted-result
          (range l)
  in final-result

insert-postcond :
  (oline : Array Char) →
  (l : Nat) →
  (nl : Array Char) →
  (p : Nat) →
  (atPos : Nat) →
  (result : Array Char) →
  insert-precond oline l nl p atPos →
  Set
insert-postcond oline l nl p atPos result h-precond =
  (arraySize result ≡ l + p) ∧
  All
    (λ i →
      indexDefault nullChar result (atPos + i) ≡
      indexDefault nullChar nl i)
    (range p) ∧
  All
    (λ i →
      indexDefault nullChar result i ≡
      indexDefault nullChar oline i)
    (range atPos) ∧
  All
    (λ i →
      indexDefault nullChar result (atPos + p + i) ≡
      indexDefault nullChar oline (atPos + i))
    (range (natSubtract l atPos))

insert-spec-satisfied : Set
insert-spec-satisfied =
  (oline : Array Char) →
  (l : Nat) →
  (nl : Array Char) →
  (p : Nat) →
  (atPos : Nat) →
  (h-precond : insert-precond oline l nl p atPos) →
  insert-postcond
    oline
    l
    nl
    p
    atPos
    (insert oline l nl p atPos h-precond)
    h-precond
