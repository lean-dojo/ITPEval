-- Statement-only formalization of VERINA corpus artifact verina_basic_44,
-- catalog title "isOddAtIndexOdd": a deterministic indexed integer-array
-- traversal returns true exactly when every odd index contains an odd integer.
-- This file contains no proof.

{-# OPTIONS --safe #-}

module VerinaBasic44 where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Int using (Int; negsuc; pos)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc)

infix 4 _≤_ _<_ _↔_

record Top : Set where
  constructor top

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

notBool : Bool → Bool
notBool true = false
notBool false = true

boolOr : Bool → Bool → Bool
boolOr true right = true
boolOr false right = right

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

oneInt : Int
oneInt = pos (suc zero)

isOdd : Int → Bool
isOdd n = intEqual (moduloByTwo n) oneInt

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

record IndexedInt : Set where
  constructor indexed
  field
    indexedPosition : Nat
    indexedValue : Int

open IndexedInt

mapIndexedFrom : Nat → Array Int → List IndexedInt
mapIndexedFrom index [] = []
mapIndexedFrom index (x ∷ xs) =
  indexed index x ∷ mapIndexedFrom (suc index) xs

allList : {A : Set} → (A → Bool) → List A → Bool
allList predicate [] = true
allList predicate (x ∷ xs) with predicate x
... | true = allList predicate xs
... | false = false

oddIndexContainsOdd : IndexedInt → Bool
oddIndexContainsOdd entry =
  boolOr
    (notBool (isOdd (pos (indexedPosition entry))))
    (isOdd (indexedValue entry))

isOddAtIndexOdd-precond : Array Int → Set
isOddAtIndexOdd-precond a = Top

isOddAtIndexOdd :
  (a : Array Int) →
  isOddAtIndexOdd-precond a →
  Bool
isOddAtIndexOdd a h-precond =
  allList
    oddIndexContainsOdd
    (mapIndexedFrom zero a)

isOddAtIndexOdd-postcond :
  (a : Array Int) →
  (result : Bool) →
  isOddAtIndexOdd-precond a →
  Set
isOddAtIndexOdd-postcond a result h-precond =
  IsTrue result ↔
  ((i : Nat) →
    (h-i : i < arraySize a) →
    IsTrue (isOdd (pos i)) →
    IsTrue (isOdd (arrayLookup a i h-i)))

isOddAtIndexOdd-spec-satisfied : Set
isOddAtIndexOdd-spec-satisfied =
  (a : Array Int) →
  (h-precond : isOddAtIndexOdd-precond a) →
  isOddAtIndexOdd-postcond
    a
    (isOddAtIndexOdd a h-precond)
    h-precond
