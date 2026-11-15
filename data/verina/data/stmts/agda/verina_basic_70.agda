-- Statement-only formalization of VERINA corpus artifact verina_basic_70,
-- catalog title "LinearSearch3": a deterministic linear search of an integer
-- array returns the first index satisfying a Boolean predicate under an
-- existence precondition and is connected to its complete correctness
-- contract. This file contains no proof.

{-# OPTIONS --safe #-}

module VerinaBasic70 where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Int using (Int; pos)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc)

infixr 3 _∧_
infix 4 _≤_ _<_

data Empty : Set where

Not : Set → Set
Not A = A → Empty

record _∧_ (A B : Set) : Set where
  constructor both
  field
    first : A
    second : B

data Exists {A : Set} (P : A → Set) : Set where
  witness : (x : A) → P x → Exists P

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

Array : Set → Set
Array A = List A

arraySize : {A : Set} → Array A → Nat
arraySize [] = zero
arraySize (_ ∷ xs) = suc (arraySize xs)

dropArray : {A : Set} → Nat → Array A → Array A
dropArray zero xs = xs
dropArray (suc n) [] = []
dropArray (suc n) (_ ∷ xs) = dropArray n xs

indexDefault : {A : Set} → A → Array A → Nat → A
indexDefault default [] index = default
indexDefault default (x ∷ xs) zero = x
indexDefault default (x ∷ xs) (suc index) =
  indexDefault default xs index

zeroInt : Int
zeroInt = pos zero

LinearSearch3-precond : Array Int → (Int → Bool) → Set
LinearSearch3-precond a P =
  Exists
    (λ i →
      (i < arraySize a) ∧
      IsTrue (P (indexDefault zeroInt a i)))

LinearSearch3-loop-from :
  Array Int →
  (Int → Bool) →
  Nat →
  Nat
LinearSearch3-loop-from [] P n = zero
LinearSearch3-loop-from (x ∷ xs) P n =
  if P x
  then n
  else LinearSearch3-loop-from xs P (suc n)

-- Dropping n entries makes structural recursion express exactly the source
-- loop's scan from index n; an exhausted suffix has the source result zero.
LinearSearch3-loop :
  Array Int →
  (Int → Bool) →
  Nat →
  Nat
LinearSearch3-loop a P n =
  LinearSearch3-loop-from (dropArray n a) P n

LinearSearch3 :
  (a : Array Int) →
  (P : Int → Bool) →
  LinearSearch3-precond a P →
  Nat
LinearSearch3 a P h-precond =
  LinearSearch3-loop a P zero

LinearSearch3-postcond :
  (a : Array Int) →
  (P : Int → Bool) →
  (result : Nat) →
  LinearSearch3-precond a P →
  Set
LinearSearch3-postcond a P result h-precond =
  (result < arraySize a) ∧
  IsTrue (P (indexDefault zeroInt a result)) ∧
  ((k : Nat) →
    k < result →
    Not (IsTrue (P (indexDefault zeroInt a k))))

LinearSearch3-spec-satisfied : Set
LinearSearch3-spec-satisfied =
  (a : Array Int) →
  (P : Int → Bool) →
  (h-precond : LinearSearch3-precond a P) →
  LinearSearch3-postcond
    a
    P
    (LinearSearch3 a P h-precond)
    h-precond
