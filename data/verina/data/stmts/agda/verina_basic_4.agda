-- Statement-only formalization of VERINA corpus artifact verina_basic_4,
-- catalog title "kthElement": a deterministic integer-array program returns
-- the element at a valid one-based index and is connected to its Boolean
-- array-membership correctness contract. This file contains no proof.

{-# OPTIONS --safe #-}

module VerinaBasic4 where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Int using (Int; negsuc; pos)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc)

infix 4 _≤_
infixr 3 _∧_

record _∧_ (A B : Set) : Set where
  constructor both
  field
    first : A
    second : B

data _≤_ : Nat → Nat → Set where
  zero≤ : {n : Nat} → zero ≤ n
  suc≤suc : {m n : Nat} → m ≤ n → suc m ≤ suc n

data IsTrue : Bool → Set where
  true-witness : IsTrue true

Array : Set → Set
Array A = List A

arraySize : {A : Set} → Array A → Nat
arraySize [] = zero
arraySize (_ ∷ xs) = suc (arraySize xs)

natPredecessor : Nat → Nat
natPredecessor zero = zero
natPredecessor (suc n) = n

indexDefault : {A : Set} → A → Array A → Nat → A
indexDefault default [] index = default
indexDefault default (x ∷ xs) zero = x
indexDefault default (x ∷ xs) (suc index) =
  indexDefault default xs index

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

boolAnd : Bool → Bool → Bool
boolAnd true right = right
boolAnd false right = false

anyList : {A : Set} → (A → Bool) → List A → Bool
anyList predicate [] = false
anyList predicate (x ∷ xs) with predicate x
... | true = true
... | false = anyList predicate xs

zeroInt : Int
zeroInt = pos zero

one : Nat
one = suc zero

kthElement-precond : Array Int → Nat → Set
kthElement-precond arr k =
  (one ≤ k) ∧ (k ≤ arraySize arr)

kthElement :
  (arr : Array Int) →
  (k : Nat) →
  kthElement-precond arr k →
  Int
kthElement arr k h-precond =
  indexDefault zeroInt arr (natPredecessor k)

kthElement-postcond :
  (arr : Array Int) →
  (k : Nat) →
  (result : Int) →
  kthElement-precond arr k →
  Set
kthElement-postcond arr k result h-precond =
  IsTrue
    (anyList
      (λ x →
        boolAnd
          (intEqual x result)
          (intEqual
            x
            (indexDefault zeroInt arr (natPredecessor k))))
      arr)

kthElement-spec-satisfied : Set
kthElement-spec-satisfied =
  (arr : Array Int) →
  (k : Nat) →
  (h-precond : kthElement-precond arr k) →
  kthElement-postcond
    arr
    k
    (kthElement arr k h-precond)
    h-precond
