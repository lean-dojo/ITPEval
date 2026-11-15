-- Statement-only formalization of VERINA corpus artifact verina_basic_49,
-- catalog title "findFirstOdd": a deterministic scan of a nonempty integer
-- array returns the least index containing an odd value, or no index exactly
-- when the array contains no odd value. This file contains no proof.

{-# OPTIONS --safe #-}

module VerinaBasic49 where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Int using (Int; negsuc; pos)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Maybe using (Maybe; just; nothing)
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

notBool : Bool → Bool
notBool true = false
notBool false = true

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

isOdd : Int → Bool
isOdd x = notBool (intEqual (moduloByTwo x) zeroInt)

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

findFirstOdd-precond : Array Int → Set
findFirstOdd-precond a = zero < arraySize a

findFirstOddFrom : Array Int → Nat → Maybe Nat
findFirstOddFrom [] index = nothing
findFirstOddFrom (x ∷ xs) index =
  if isOdd x
  then just index
  else findFirstOddFrom xs (suc index)

findFirstOdd :
  (a : Array Int) →
  findFirstOdd-precond a →
  Maybe Nat
findFirstOdd a h-precond =
  findFirstOddFrom a zero

findFirstOdd-postcond :
  (a : Array Int) →
  (result : Maybe Nat) →
  findFirstOdd-precond a →
  Set
findFirstOdd-postcond a (just idx) h-precond =
  (idx < arraySize a) ∧
  IsTrue (isOdd (indexDefault zeroInt a idx)) ∧
  ((j : Nat) →
    j < idx →
    Not (IsTrue (isOdd (indexDefault zeroInt a j))))
findFirstOdd-postcond a nothing h-precond =
  (i : Nat) →
  i < arraySize a →
  Not (IsTrue (isOdd (indexDefault zeroInt a i)))

findFirstOdd-spec-satisfied : Set
findFirstOdd-spec-satisfied =
  (a : Array Int) →
  (h-precond : findFirstOdd-precond a) →
  findFirstOdd-postcond
    a
    (findFirstOdd a h-precond)
    h-precond
