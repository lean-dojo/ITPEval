-- Statement-only formalization of VERINA corpus artifact verina_basic_10,
-- catalog title "isGreater": a deterministic array traversal returns whether
-- an integer is strictly greater than every array element and is connected to
-- its indexed Boolean correctness contract. This file contains no proof.

{-# OPTIONS --safe #-}

module VerinaBasic10 where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Int using (Int; negsuc; pos)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc)

infix 4 _≤_ _<_ _↔_

data _≤_ : Nat → Nat → Set where
  zero≤ : {n : Nat} → zero ≤ n
  suc≤suc : {m n : Nat} → m ≤ n → suc m ≤ suc n

_<_ : Nat → Nat → Set
m < n = suc m ≤ n

record _↔_ (A B : Set) : Set where
  constructor iff
  field
    forward : A → B
    backward : B → A

data IsTrue : Bool → Set where
  true-witness : IsTrue true

natLess : Nat → Nat → Bool
natLess zero zero = false
natLess zero (suc _) = true
natLess (suc _) zero = false
natLess (suc m) (suc n) = natLess m n

intLess : Int → Int → Bool
intLess (pos m) (pos n) = natLess m n
intLess (pos _) (negsuc _) = false
intLess (negsuc _) (pos _) = true
intLess (negsuc m) (negsuc n) = natLess n m

IntLess : Int → Int → Set
IntLess x y = IsTrue (intLess x y)

Array : Set → Set
Array A = List A

arraySize : {A : Set} → Array A → Nat
arraySize [] = zero
arraySize (_ ∷ xs) = suc (arraySize xs)

arrayLookup :
  {A : Set} →
  (a : Array A) →
  (i : Nat) →
  i < arraySize a →
  A
arrayLookup [] i ()
arrayLookup (x ∷ xs) zero h-i = x
arrayLookup (x ∷ xs) (suc i) (suc≤suc h-i) =
  arrayLookup xs i h-i

allList : {A : Set} → (A → Bool) → List A → Bool
allList predicate [] = true
allList predicate (x ∷ xs) with predicate x
... | true = allList predicate xs
... | false = false

isGreater-precond : Int → Array Int → Set
isGreater-precond n a = zero < arraySize a

isGreater :
  (n : Int) →
  (a : Array Int) →
  isGreater-precond n a →
  Bool
isGreater n a h-precond =
  allList (λ x → intLess x n) a

isGreater-postcond :
  (n : Int) →
  (a : Array Int) →
  (result : Bool) →
  isGreater-precond n a →
  Set
isGreater-postcond n a result h-precond =
  ((i : Nat) →
    (h-i : i < arraySize a) →
    IntLess (arrayLookup a i h-i) n)
  ↔ IsTrue result

isGreater-spec-satisfied : Set
isGreater-spec-satisfied =
  (n : Int) →
  (a : Array Int) →
  (h-precond : isGreater-precond n a) →
  isGreater-postcond
    n
    a
    (isGreater n a h-precond)
    h-precond
