-- Statement-only formalization of VERINA corpus artifact verina_basic_24,
-- catalog title "firstEvenOddDifference": a deterministic integer-array scan
-- returns the first even entry minus the first odd entry and is connected to
-- the corresponding first-occurrence correctness contract.
-- This file contains no proof.

{-# OPTIONS --safe #-}

module VerinaBasic24 where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Int using (Int; negsuc; pos)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Maybe using (Maybe; just; nothing)
open import Agda.Builtin.Nat using (Nat; zero; suc)

infixr 3 _∧_
infix 4 _≤_ _<_ _∈_

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

isEven : Int → Bool
isEven n = intEqual (moduloByTwo n) zeroInt

isOdd : Int → Bool
isOdd n = notBool (intEqual (moduloByTwo n) zeroInt)

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

data _∈_ {A : Set} (x : A) : List A → Set where
  here : {xs : List A} → x ∈ (x ∷ xs)
  there :
    {y : A} {xs : List A} →
    x ∈ xs →
    x ∈ (y ∷ xs)

one : Nat
one = suc zero

firstEvenOddDifference-precond : Array Int → Set
firstEvenOddDifference-precond a =
  (one < arraySize a) ∧
  Exists (λ x → (x ∈ a) ∧ IsTrue (isEven x)) ∧
  Exists (λ x → (x ∈ a) ∧ IsTrue (isOdd x))

updateFirst : Bool → Nat → Maybe Nat → Maybe Nat
updateFirst predicate index nothing =
  if predicate then just index else nothing
updateFirst predicate index current@(just _) = current

findFirstEvenOdd :
  Array Int →
  List Int →
  Nat →
  Maybe Nat →
  Maybe Nat →
  Int
findFirstEvenOdd a [] index firstEven firstOdd = zeroInt
findFirstEvenOdd a (x ∷ xs) index firstEven firstOdd
  with updateFirst (isEven x) index firstEven
     | updateFirst (isOdd x) index firstOdd
... | just evenIndex | just oddIndex =
  intSubtract
    (indexDefault zeroInt a evenIndex)
    (indexDefault zeroInt a oddIndex)
... | nothing | nothing =
  findFirstEvenOdd a xs (suc index) nothing nothing
... | nothing | updatedOdd@(just _) =
  findFirstEvenOdd a xs (suc index) nothing updatedOdd
... | updatedEven@(just _) | nothing =
  findFirstEvenOdd a xs (suc index) updatedEven nothing

firstEvenOddDifference :
  (a : Array Int) →
  firstEvenOddDifference-precond a →
  Int
firstEvenOddDifference a h-precond =
  findFirstEvenOdd a a zero nothing nothing

firstEvenOddDifference-postcond :
  (a : Array Int) →
  (result : Int) →
  firstEvenOddDifference-precond a →
  Set
firstEvenOddDifference-postcond a result h-precond =
  Exists
    (λ i →
      Exists
        (λ j →
          (i < arraySize a) ∧
          (j < arraySize a) ∧
          IsTrue (isEven (indexDefault zeroInt a i)) ∧
          IsTrue (isOdd (indexDefault zeroInt a j)) ∧
          (result ≡
            intSubtract
              (indexDefault zeroInt a i)
              (indexDefault zeroInt a j)) ∧
          ((k : Nat) →
            k < i →
            IsTrue (isOdd (indexDefault zeroInt a k))) ∧
          ((k : Nat) →
            k < j →
            IsTrue (isEven (indexDefault zeroInt a k)))))

firstEvenOddDifference-spec-satisfied : Set
firstEvenOddDifference-spec-satisfied =
  (a : Array Int) →
  (h-precond : firstEvenOddDifference-precond a) →
  firstEvenOddDifference-postcond
    a
    (firstEvenOddDifference a h-precond)
    h-precond
