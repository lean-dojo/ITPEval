-- Statement-only formalization of VERINA corpus artifact verina_basic_9,
-- catalog title "hasCommonElement": a deterministic nested array traversal
-- returns whether two nonempty integer arrays share an element and is connected
-- to its bounded-index Boolean correctness contract. This file contains no proof.

{-# OPTIONS --safe #-}

module VerinaBasic9 where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Int using (Int; negsuc; pos)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc)

infix 4 _≤_ _<_ _↔_
infixr 3 _∧_

data _≤_ : Nat → Nat → Set where
  zero≤ : {n : Nat} → zero ≤ n
  suc≤suc : {m n : Nat} → m ≤ n → suc m ≤ suc n

_<_ : Nat → Nat → Set
m < n = suc m ≤ n

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

record Exists (A : Set) (P : A → Set) : Set where
  constructor exists
  field
    witness : A
    property : P witness

data IsTrue : Bool → Set where
  true-witness : IsTrue true

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

indexDefault : {A : Set} → A → Array A → Nat → A
indexDefault default [] index = default
indexDefault default (x ∷ xs) zero = x
indexDefault default (x ∷ xs) (suc index) =
  indexDefault default xs index

anyList : {A : Set} → (A → Bool) → List A → Bool
anyList predicate [] = false
anyList predicate (x ∷ xs) with predicate x
... | true = true
... | false = anyList predicate xs

hasCommonElement-precond :
  Array Int →
  Array Int →
  Set
hasCommonElement-precond a b =
  (zero < arraySize a) ∧ (zero < arraySize b)

hasCommonElement :
  (a b : Array Int) →
  hasCommonElement-precond a b →
  Bool
hasCommonElement a b h-precond =
  anyList
    (λ x → anyList (λ y → intEqual x y) b)
    a

hasCommonElement-postcond :
  (a b : Array Int) →
  (result : Bool) →
  hasCommonElement-precond a b →
  Set
hasCommonElement-postcond a b result h-precond =
  Exists Nat
    (λ i →
      Exists Nat
        (λ j →
          (i < arraySize a) ∧
          ((j < arraySize b) ∧
           (indexDefault (pos zero) a i ≡
            indexDefault (pos zero) b j))))
  ↔ IsTrue result

hasCommonElement-spec-satisfied : Set
hasCommonElement-spec-satisfied =
  (a b : Array Int) →
  (h-precond : hasCommonElement-precond a b) →
  hasCommonElement-postcond
    a
    b
    (hasCommonElement a b h-precond)
    h-precond
