-- Statement-only formalization of VERINA corpus artifact verina_basic_69,
-- catalog title "LinearSearch": a deterministic recursive linear search of an
-- integer array returns its first target index under an existence precondition
-- and is connected to its complete correctness contract. This file contains no proof.

{-# OPTIONS --safe #-}

module VerinaBasic69 where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Int using (Int; negsuc; pos)
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

data _≤_ : Nat → Nat → Set where
  zero≤ : {n : Nat} → zero ≤ n
  suc≤suc : {m n : Nat} → m ≤ n → suc m ≤ suc n

_<_ : Nat → Nat → Set
m < n = suc m ≤ n

if_then_else_ : {A : Set} → Bool → A → A → A
if true then when-true else when-false = when-true
if false then when-true else when-false = when-false

natEqual : Nat → Nat → Bool
natEqual zero zero = true
natEqual zero (suc _) = false
natEqual (suc _) zero = false
natEqual (suc m) (suc n) = natEqual m n

intEqual : Int → Int → Bool
intEqual (pos m) (pos n) = natEqual m n
intEqual (pos _) (negsuc _) = false
intEqual (negsuc _) (pos _) = false
intEqual (negsuc m) (negsuc n) = natEqual m n

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

LinearSearch-precond : Array Int → Int → Set
LinearSearch-precond a e =
  Exists
    (λ i →
      (i < arraySize a) ∧
      (indexDefault zeroInt a i ≡ e))

linearSearchAuxFrom :
  Array Int →
  Int →
  Nat →
  Nat
linearSearchAuxFrom [] e n = zero
linearSearchAuxFrom (x ∷ xs) e n =
  if intEqual x e
  then n
  else linearSearchAuxFrom xs e (suc n)

-- Dropping n entries makes structural recursion express exactly the source
-- helper's scan from index n; an exhausted suffix has the source result zero.
linearSearchAux :
  Array Int →
  Int →
  Nat →
  Nat
linearSearchAux a e n =
  linearSearchAuxFrom (dropArray n a) e n

LinearSearch :
  (a : Array Int) →
  (e : Int) →
  LinearSearch-precond a e →
  Nat
LinearSearch a e h-precond =
  linearSearchAux a e zero

LinearSearch-postcond :
  (a : Array Int) →
  (e : Int) →
  (result : Nat) →
  LinearSearch-precond a e →
  Set
LinearSearch-postcond a e result h-precond =
  (result < arraySize a) ∧
  (indexDefault zeroInt a result ≡ e) ∧
  ((k : Nat) →
    k < result →
    Not (indexDefault zeroInt a k ≡ e))

LinearSearch-spec-satisfied : Set
LinearSearch-spec-satisfied =
  (a : Array Int) →
  (e : Int) →
  (h-precond : LinearSearch-precond a e) →
  LinearSearch-postcond
    a
    e
    (LinearSearch a e h-precond)
    h-precond
