-- Statement-only formalization of VERINA corpus artifact verina_basic_41,
-- catalog title "hasOnlyOneDistinctElement": a deterministic integer-array
-- scan checks whether every entry equals the first and is connected to its
-- pairwise-equality and differing-entry correctness contract. This file
-- contains no proof.

{-# OPTIONS --safe #-}

module VerinaBasic41 where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Int using (Int; negsuc; pos)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc)

infixr 3 _∧_
infix 4 _≤_ _<_

record Top : Set where
  constructor top

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

notBool : Bool → Bool
notBool true = false
notBool false = true

allList : {A : Set} → (A → Bool) → List A → Bool
allList predicate [] = true
allList predicate (x ∷ xs) =
  if predicate x
  then allList predicate xs
  else false

anyList : {A : Set} → (A → Bool) → List A → Bool
anyList predicate [] = false
anyList predicate (x ∷ xs) =
  if predicate x
  then true
  else anyList predicate xs

All : {A : Set} → (A → Set) → List A → Set
All predicate [] = Top
All predicate (x ∷ xs) =
  predicate x ∧ All predicate xs

Pairwise :
  {A : Set} →
  (A → A → Set) →
  List A →
  Set
Pairwise relation [] = Top
Pairwise relation (x ∷ xs) =
  All (relation x) xs ∧ Pairwise relation xs

Array : Set → Set
Array A = List A

arraySize : {A : Set} → Array A → Nat
arraySize [] = zero
arraySize (_ ∷ xs) = suc (arraySize xs)

zeroInt : Int
zeroInt = pos zero

headDefault : {A : Set} → A → List A → A
headDefault default [] = default
headDefault default (x ∷ xs) = x

hasOnlyOneDistinctElement-precond : Array Int → Set
hasOnlyOneDistinctElement-precond a =
  zero < arraySize a

scanEqualToFirst : Int → List Int → Bool
scanEqualToFirst firstElement [] = true
scanEqualToFirst firstElement (x ∷ xs) =
  if intEqual x firstElement
  then scanEqualToFirst firstElement xs
  else false

hasOnlyOneDistinctElement :
  (a : Array Int) →
  hasOnlyOneDistinctElement-precond a →
  Bool
hasOnlyOneDistinctElement [] h-precond = true
hasOnlyOneDistinctElement (firstElement ∷ rest) h-precond =
  scanEqualToFirst firstElement rest

hasOnlyOneDistinctElement-postcond :
  (a : Array Int) →
  (result : Bool) →
  hasOnlyOneDistinctElement-precond a →
  Set
hasOnlyOneDistinctElement-postcond a result h-precond =
  (IsTrue result →
    Pairwise (λ x y → x ≡ y) a) ∧
  (Not (IsTrue result) →
    IsTrue
      (anyList
        (λ x →
          notBool
            (intEqual x (headDefault zeroInt a)))
        a))

hasOnlyOneDistinctElement-spec-satisfied : Set
hasOnlyOneDistinctElement-spec-satisfied =
  (a : Array Int) →
  (h-precond : hasOnlyOneDistinctElement-precond a) →
  hasOnlyOneDistinctElement-postcond
    a
    (hasOnlyOneDistinctElement a h-precond)
    h-precond
