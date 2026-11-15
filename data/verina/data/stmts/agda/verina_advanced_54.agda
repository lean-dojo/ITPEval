-- Statement-only formalization of VERINA corpus artifact verina_advanced_54,
-- catalog title "missingNumber": a deterministic arithmetic program returns
-- the missing natural number from a distinct list bounded by its length.
-- This file contains no proof.

{-# OPTIONS --safe #-}

module VerinaAdvanced54 where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using
  (Nat; zero; suc; _+_; _*_; div-helper)

infixr 3 _∧_
infix 4 _∈_

data Empty : Set where

Not : Set → Set
Not A = A → Empty

record Top : Set where
  constructor top

record _∧_ (A B : Set) : Set where
  constructor both
  field
    first : A
    second : B

data IsTrue : Bool → Set where
  true-witness : IsTrue true

if_then_else_ : {A : Set} → Bool → A → A → A
if true then when-true else when-false = when-true
if false then when-true else when-false = when-false

natLessOrEqual : Nat → Nat → Bool
natLessOrEqual zero _ = true
natLessOrEqual (suc _) zero = false
natLessOrEqual (suc m) (suc n) = natLessOrEqual m n

natSubtract : Nat → Nat → Nat
natSubtract m zero = m
natSubtract zero (suc n) = zero
natSubtract (suc m) (suc n) = natSubtract m n

naturalDiv : Nat → Nat → Nat
naturalDiv numerator zero = zero
naturalDiv numerator (suc denominator) =
  div-helper zero denominator numerator denominator

one : Nat
one = suc zero

two : Nat
two = suc one

listLength : {A : Set} → List A → Nat
listLength [] = zero
listLength (_ ∷ xs) = suc (listLength xs)

foldLeft : {A B : Set} → (A → B → A) → A → List B → A
foldLeft step accumulator [] = accumulator
foldLeft step accumulator (x ∷ xs) =
  foldLeft step (step accumulator x) xs

allList : {A : Set} → (A → Bool) → List A → Bool
allList predicate [] = true
allList predicate (x ∷ xs) =
  if predicate x
  then allList predicate xs
  else false

data _∈_ (x : Nat) : List Nat → Set where
  here : {xs : List Nat} → x ∈ (x ∷ xs)
  there : {y : Nat} {xs : List Nat} → x ∈ xs → x ∈ (y ∷ xs)

NoDuplicates : List Nat → Set
NoDuplicates [] = Top
NoDuplicates (x ∷ xs) =
  Not (x ∈ xs) ∧ NoDuplicates xs

missingNumber-precond : List Nat → Set
missingNumber-precond nums =
  IsTrue
    (allList
      (λ x → natLessOrEqual x (listLength nums))
      nums) ∧
  NoDuplicates nums

missingNumber :
  (nums : List Nat) →
  missingNumber-precond nums →
  Nat
missingNumber nums h-precond =
  let n = listLength nums
      expected-sum = naturalDiv (n * (n + one)) two
      actual-sum = foldLeft _+_ zero nums
  in
    natSubtract expected-sum actual-sum

rangeFrom : Nat → Nat → List Nat
rangeFrom start zero = []
rangeFrom start (suc count) =
  start ∷ rangeFrom (suc start) count

range : Nat → List Nat
range n = rangeFrom zero n

missingNumber-postcond :
  (nums : List Nat) →
  (result : Nat) →
  missingNumber-precond nums →
  Set
missingNumber-postcond nums result h-precond =
  let n = listLength nums
  in
    (result ∈ range (n + one)) ∧
    (Not (result ∈ nums) ∧
    ((x : Nat) →
      x ∈ range (n + one) →
      Not (x ≡ result) →
      x ∈ nums))

missingNumber-spec-satisfied : Set
missingNumber-spec-satisfied =
  (nums : List Nat) →
  (h-precond : missingNumber-precond nums) →
  missingNumber-postcond
    nums
    (missingNumber nums h-precond)
    h-precond
