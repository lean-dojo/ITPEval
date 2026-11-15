-- Statement-only formalization of VERINA corpus artifact verina_basic_60,
-- catalog title "FindEvenNumbers": a deterministic integer-array scan keeps
-- exactly the even entries in input order and is connected to its all-even,
-- ordered-sublist, and filtered-count correctness contract. This file contains no proof.

{-# OPTIONS --safe #-}

module VerinaBasic60 where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Int using (Int; negsuc; pos)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc)

infixr 3 _∧_

record Top : Set where
  constructor top

record _∧_ (A B : Set) : Set where
  constructor both
  field
    first : A
    second : B

data IsTrue : Bool → Set where
  true-witness : IsTrue true

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

listLength : {A : Set} → List A → Nat
listLength [] = zero
listLength (_ ∷ xs) = suc (listLength xs)

allList : {A : Set} → (A → Bool) → List A → Bool
allList predicate [] = true
allList predicate (x ∷ xs) =
  if predicate x
  then allList predicate xs
  else false

countP : {A : Set} → (A → Bool) → List A → Nat
countP predicate [] = zero
countP predicate (x ∷ xs) =
  if predicate x
  then suc (countP predicate xs)
  else countP predicate xs

data Sublist {A : Set} : List A → List A → Set where
  sublistNil :
    Sublist [] []

  sublistDrop :
    {xs ys : List A} {y : A} →
    Sublist xs ys →
    Sublist xs (y ∷ ys)

  sublistKeep :
    {xs ys : List A} {x : A} →
    Sublist xs ys →
    Sublist (x ∷ xs) (x ∷ ys)

FindEvenNumbers-precond : Array Int → Set
FindEvenNumbers-precond arr = Top

FindEvenNumbers-loop :
  Array Int →
  Array Int →
  Array Int
FindEvenNumbers-loop [] accumulator = accumulator
FindEvenNumbers-loop (x ∷ xs) accumulator =
  if isEven x
  then FindEvenNumbers-loop xs (snoc accumulator x)
  else FindEvenNumbers-loop xs accumulator

FindEvenNumbers :
  (arr : Array Int) →
  FindEvenNumbers-precond arr →
  Array Int
FindEvenNumbers arr h-precond =
  FindEvenNumbers-loop arr []

FindEvenNumbers-postcond :
  (arr : Array Int) →
  (result : Array Int) →
  FindEvenNumbers-precond arr →
  Set
FindEvenNumbers-postcond arr result h-precond =
  IsTrue (allList isEven result) ∧
  Sublist result arr ∧
  (listLength result ≡ countP isEven arr)

FindEvenNumbers-spec-satisfied : Set
FindEvenNumbers-spec-satisfied =
  (arr : Array Int) →
  (h-precond : FindEvenNumbers-precond arr) →
  FindEvenNumbers-postcond
    arr
    (FindEvenNumbers arr h-precond)
    h-precond
