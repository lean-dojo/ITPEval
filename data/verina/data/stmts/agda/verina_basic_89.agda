-- Statement-only formalization of VERINA corpus artifact verina_basic_89,
-- catalog title "SetToSeq": a deterministic left-fold removes duplicate
-- integers while preserving first-occurrence order and is connected to its
-- membership, uniqueness, and index-order correctness contract. This file contains no proof.

{-# OPTIONS --safe #-}

module VerinaBasic89 where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Int using (Int; negsuc; pos)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc)

infixr 3 _∧_
infix 4 _≤_ _<_

record Top : Set where
  constructor top

record _∧_ (A B : Set) : Set where
  constructor both
  field
    first : A
    second : B

data _≤_ : Nat → Nat → Set where
  zero≤ : {n : Nat} → zero ≤ n
  suc≤suc : {m n : Nat} → m ≤ n → suc m ≤ suc n

_<_ : Nat → Nat → Set
m < n = suc m ≤ n

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

appendList : {A : Set} → List A → List A → List A
appendList [] ys = ys
appendList (x ∷ xs) ys = x ∷ appendList xs ys

containsInt : Int → List Int → Bool
containsInt sought [] = false
containsInt sought (x ∷ xs) =
  if intEqual sought x
  then true
  else containsInt sought xs

foldLeft :
  {A B : Set} →
  (A → B → A) →
  A →
  List B →
  A
foldLeft step accumulator [] = accumulator
foldLeft step accumulator (x ∷ xs) =
  foldLeft step (step accumulator x) xs

setToSeqStep : List Int → Int → List Int
setToSeqStep accumulator x =
  if containsInt x accumulator
  then accumulator
  else appendList accumulator (x ∷ [])

SetToSeq-precond : List Int → Set
SetToSeq-precond s = Top

SetToSeq :
  (s : List Int) →
  SetToSeq-precond s →
  List Int
SetToSeq s h-precond =
  foldLeft setToSeqStep [] s

countInt : Int → List Int → Nat
countInt sought [] = zero
countInt sought (x ∷ xs) =
  if intEqual sought x
  then suc (countInt sought xs)
  else countInt sought xs

idxOfInt : Int → List Int → Nat
idxOfInt sought [] = zero
idxOfInt sought (x ∷ xs) =
  if intEqual sought x
  then zero
  else suc (idxOfInt sought xs)

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

SetToSeq-postcond :
  (s : List Int) →
  (result : List Int) →
  SetToSeq-precond s →
  Set
SetToSeq-postcond s result h-precond =
  All (λ a → IsTrue (containsInt a s)) result ∧
  All (λ a → IsTrue (containsInt a result)) s ∧
  All (λ a → countInt a result ≡ suc zero) result ∧
  Pairwise
    (λ a b →
      idxOfInt a result < idxOfInt b result →
      idxOfInt a s < idxOfInt b s)
    result

SetToSeq-spec-satisfied : Set
SetToSeq-spec-satisfied =
  (s : List Int) →
  (h-precond : SetToSeq-precond s) →
  SetToSeq-postcond
    s
    (SetToSeq s h-precond)
    h-precond
