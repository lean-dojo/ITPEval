-- Statement-only formalization of VERINA corpus artifact verina_basic_68,
-- catalog title "LinearSearch": a deterministic linear search of an integer
-- array returns its first target index, or the array size when absent, and is
-- connected to its complete first-occurrence contract. This file contains no proof.

{-# OPTIONS --safe #-}

module VerinaBasic68 where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Int using (Int; negsuc; pos)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc)

infixr 2 _∨_
infixr 3 _∧_
infix 4 _≤_ _<_

record Top : Set where
  constructor top

data Empty : Set where

Not : Set → Set
Not A = A → Empty

data _∨_ (A B : Set) : Set where
  left : A → A ∨ B
  right : B → A ∨ B

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
LinearSearch-precond a e = Top

LinearSearch-loop-from :
  Array Int →
  Int →
  Nat →
  Nat
LinearSearch-loop-from [] e index = index
LinearSearch-loop-from (x ∷ xs) e index =
  if intEqual x e
  then index
  else LinearSearch-loop-from xs e (suc index)

LinearSearch-loop :
  Array Int →
  Int →
  Nat →
  Nat
LinearSearch-loop a e index =
  LinearSearch-loop-from (dropArray index a) e index

LinearSearch :
  (a : Array Int) →
  (e : Int) →
  LinearSearch-precond a e →
  Nat
LinearSearch a e h-precond =
  LinearSearch-loop a e zero

LinearSearch-postcond :
  (a : Array Int) →
  (e : Int) →
  (result : Nat) →
  LinearSearch-precond a e →
  Set
LinearSearch-postcond a e result h-precond =
  (result ≤ arraySize a) ∧
  ((result ≡ arraySize a) ∨
    (indexDefault zeroInt a result ≡ e)) ∧
  ((i : Nat) →
    i < result →
    Not (indexDefault zeroInt a i ≡ e))

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
