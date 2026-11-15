-- Statement-only formalization of VERINA corpus artifact verina_basic_47,
-- catalog title "arraySum": a deterministic program sums every element of a
-- nonempty integer array and is connected to its recursive indexed-sum
-- correctness contract. This file contains no proof.

{-# OPTIONS --safe #-}

module VerinaBasic47 where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Int using (Int; negsuc; pos)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc)

infixr 3 _∧_
infix 4 _≤_ _<_

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

natLessOrEqual : Nat → Nat → Bool
natLessOrEqual zero n = true
natLessOrEqual (suc m) zero = false
natLessOrEqual (suc m) (suc n) =
  natLessOrEqual m n

intLessOrEqual : Int → Int → Bool
intLessOrEqual (pos m) (pos n) = natLessOrEqual m n
intLessOrEqual (pos m) (negsuc n) = false
intLessOrEqual (negsuc m) (pos n) = true
intLessOrEqual (negsuc m) (negsuc n) =
  natLessOrEqual n m

IntLessOrEqual : Int → Int → Set
IntLessOrEqual x y = IsTrue (intLessOrEqual x y)

intSuccessor : Int → Int
intSuccessor (pos n) = pos (suc n)
intSuccessor (negsuc zero) = pos zero
intSuccessor (negsuc (suc n)) = negsuc n

intPredecessor : Int → Int
intPredecessor (pos zero) = negsuc zero
intPredecessor (pos (suc n)) = pos n
intPredecessor (negsuc n) = negsuc (suc n)

intAdd : Int → Int → Int
intAdd x (pos zero) = x
intAdd x (pos (suc n)) =
  intSuccessor (intAdd x (pos n))
intAdd x (negsuc zero) = intPredecessor x
intAdd x (negsuc (suc n)) =
  intPredecessor (intAdd x (negsuc n))

intNegate : Int → Int
intNegate (pos zero) = pos zero
intNegate (pos (suc n)) = negsuc n
intNegate (negsuc n) = pos (suc n)

intSubtract : Int → Int → Int
intSubtract x y = intAdd x (intNegate y)

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

sumList : List Int → Int
sumList [] = zeroInt
sumList (x ∷ xs) = intAdd x (sumList xs)

arraySum-precond : Array Int → Set
arraySum-precond a = zero < arraySize a

arraySum :
  (a : Array Int) →
  arraySum-precond a →
  Int
arraySum a h-precond = sumList a

sumTo : Array Int → Nat → Int
sumTo a zero = zeroInt
sumTo a (suc n) =
  intAdd
    (sumTo a n)
    (indexDefault zeroInt a n)

arraySum-postcond :
  (a : Array Int) →
  (result : Int) →
  arraySum-precond a →
  Set
arraySum-postcond a result h-precond =
  (intSubtract result (sumTo a (arraySize a)) ≡ zeroInt) ∧
  IntLessOrEqual (sumTo a (arraySize a)) result

arraySum-spec-satisfied : Set
arraySum-spec-satisfied =
  (a : Array Int) →
  (h-precond : arraySum-precond a) →
  arraySum-postcond
    a
    (arraySum a h-precond)
    h-precond
