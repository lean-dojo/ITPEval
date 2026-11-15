-- Statement-only formalization of VERINA corpus artifact verina_basic_34,
-- catalog title "findEvenNumbers": a deterministic integer-array fold extracts
-- exactly the even entries in input order and is connected to its membership,
-- multiplicity, and first-occurrence-order correctness contract. This file
-- contains no proof.

{-# OPTIONS --safe #-}

module VerinaBasic34 where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Int using (Int; negsuc; pos)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc)

infixr 3 _∧_
infix 4 _≤_ _∈_

record Top : Set where
  constructor top

record _∧_ (A B : Set) : Set where
  constructor both
  field
    first : A
    second : B

data IsTrue : Bool → Set where
  true-witness : IsTrue true

data _≤_ : Nat → Nat → Set where
  zero≤ : {n : Nat} → zero ≤ n
  suc≤suc : {m n : Nat} → m ≤ n → suc m ≤ suc n

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

naturalModTwo : Nat → Nat
naturalModTwo zero = zero
naturalModTwo (suc zero) = suc zero
naturalModTwo (suc (suc n)) = naturalModTwo n

-- Lean remainder modulo positive two is the nonnegative parity remainder.
moduloByTwo : Int → Int
moduloByTwo (pos n) = pos (naturalModTwo n)
moduloByTwo (negsuc n) = pos (naturalModTwo (suc n))

zeroInt : Int
zeroInt = pos zero

isEven : Int → Bool
isEven n = intEqual (moduloByTwo n) zeroInt

Array : Set → Set
Array A = List A

snoc : {A : Set} → List A → A → List A
snoc [] x = x ∷ []
snoc (y ∷ ys) x = y ∷ snoc ys x

foldl :
  {A B : Set} →
  (A → B → A) →
  A →
  List B →
  A
foldl step accumulator [] = accumulator
foldl step accumulator (x ∷ xs) =
  foldl step (step accumulator x) xs

filterEvenStep : Array Int → Int → Array Int
filterEvenStep accumulator x =
  if isEven x
  then snoc accumulator x
  else accumulator

All : {A : Set} → (A → Set) → List A → Set
All predicate [] = Top
All predicate (x ∷ xs) =
  predicate x ∧ All predicate xs

data _∈_ {A : Set} (x : A) : List A → Set where
  here : {xs : List A} → x ∈ (x ∷ xs)
  there :
    {y : A} {xs : List A} →
    x ∈ xs →
    x ∈ (y ∷ xs)

count : Int → List Int → Nat
count x [] = zero
count x (y ∷ ys) =
  if intEqual x y
  then suc (count x ys)
  else count x ys

idxOf : Int → List Int → Nat
idxOf x [] = zero
idxOf x (y ∷ ys) =
  if intEqual x y
  then zero
  else suc (idxOf x ys)

findEvenNumbers-precond : Array Int → Set
findEvenNumbers-precond arr = Top

findEvenNumbers :
  (arr : Array Int) →
  findEvenNumbers-precond arr →
  Array Int
findEvenNumbers arr h-precond =
  foldl filterEvenStep [] arr

findEvenNumbers-postcond :
  (arr : Array Int) →
  (result : Array Int) →
  findEvenNumbers-precond arr →
  Set
findEvenNumbers-postcond arr result h-precond =
  All
    (λ x →
      IsTrue (isEven x) ∧
      (x ∈ arr) ∧
      (count x result ≡ count x arr))
    result ∧
  All
    (λ x →
      IsTrue (isEven x) →
      x ∈ result)
    arr ∧
  All
    (λ x →
      All
        (λ y →
          IsTrue (isEven x) →
          IsTrue (isEven y) →
          idxOf x arr ≤ idxOf y arr →
          idxOf x result ≤ idxOf y result)
        arr)
    arr

findEvenNumbers-spec-satisfied : Set
findEvenNumbers-spec-satisfied =
  (arr : Array Int) →
  (h-precond : findEvenNumbers-precond arr) →
  findEvenNumbers-postcond
    arr
    (findEvenNumbers arr h-precond)
    h-precond
