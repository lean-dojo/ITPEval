-- Statement-only formalization of VERINA corpus artifact verina_basic_15,
-- catalog title "containsConsecutiveNumbers": a deterministic integer-array
-- scan reports whether some adjacent element is the successor of its
-- predecessor and is connected to its existential correctness contract.
-- This file contains no proof.

{-# OPTIONS --safe #-}

module VerinaBasic15 where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Int using (Int; negsuc; pos)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _-_)

infix 2 _↔_
infixr 3 _∧_
infix 4 _≤_ _<_
infixr 5 _||_

record Top : Set where
  constructor top

record _∧_ (A B : Set) : Set where
  constructor both
  field
    first : A
    second : B

record _↔_ (A B : Set) : Set where
  constructor iff
  field
    forward : A → B
    backward : B → A

data Exists {A : Set} (P : A → Set) : Set where
  witness : (x : A) → P x → Exists P

data IsTrue : Bool → Set where
  true-witness : IsTrue true

_||_ : Bool → Bool → Bool
true || other = true
false || other = other

data _≤_ : Nat → Nat → Set where
  zero≤ : {n : Nat} → zero ≤ n
  suc≤suc : {m n : Nat} → m ≤ n → suc m ≤ suc n

_<_ : Nat → Nat → Set
m < n = suc m ≤ n

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

intSuccessor : Int → Int
intSuccessor (pos n) = pos (suc n)
intSuccessor (negsuc zero) = pos zero
intSuccessor (negsuc (suc n)) = negsuc n

one : Nat
one = suc zero

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

containsConsecutiveNumbers-scan : Array Int → Bool
containsConsecutiveNumbers-scan [] = false
containsConsecutiveNumbers-scan (x ∷ []) = false
containsConsecutiveNumbers-scan (x ∷ y ∷ rest) =
  intEqual (intSuccessor x) y ||
  containsConsecutiveNumbers-scan (y ∷ rest)

containsConsecutiveNumbers-precond : Array Int → Set
containsConsecutiveNumbers-precond a = Top

containsConsecutiveNumbers :
  (a : Array Int) →
  containsConsecutiveNumbers-precond a →
  Bool
containsConsecutiveNumbers a h-precond =
  containsConsecutiveNumbers-scan a

containsConsecutiveNumbers-postcond :
  (a : Array Int) →
  (result : Bool) →
  containsConsecutiveNumbers-precond a →
  Set
containsConsecutiveNumbers-postcond a result h-precond =
  Exists
    (λ i →
      (i < (arraySize a - one)) ∧
      (intSuccessor (indexDefault zeroInt a i) ≡
       indexDefault zeroInt a (i + one)))
  ↔ IsTrue result

containsConsecutiveNumbers-spec-satisfied : Set
containsConsecutiveNumbers-spec-satisfied =
  (a : Array Int) →
  (h-precond : containsConsecutiveNumbers-precond a) →
  containsConsecutiveNumbers-postcond
    a
    (containsConsecutiveNumbers a h-precond)
    h-precond
