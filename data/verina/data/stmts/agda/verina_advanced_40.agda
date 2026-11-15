-- Statement-only formalization of VERINA corpus artifact verina_advanced_40,
-- catalog title "maxOfList": a deterministic recursive program returns a
-- maximum member of a nonempty list of natural numbers. This file contains no
-- proof.

{-# OPTIONS --safe #-}

module VerinaAdvanced40 where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc)

infixr 3 _∧_
infix 4 _≤_ _∈_

data Empty : Set where

Not : Set → Set
Not A = A → Empty

record _∧_ (A B : Set) : Set where
  constructor both
  field
    first : A
    second : B

data _≤_ : Nat → Nat → Set where
  zero≤ : {n : Nat} → zero ≤ n
  suc≤suc : {m n : Nat} → m ≤ n → suc m ≤ suc n

if_then_else_ : {A : Set} → Bool → A → A → A
if true then when-true else when-false = when-true
if false then when-true else when-false = when-false

natLess : Nat → Nat → Bool
natLess zero zero = false
natLess zero (suc _) = true
natLess (suc _) zero = false
natLess (suc m) (suc n) = natLess m n

data _∈_ (x : Nat) : List Nat → Set where
  here : {xs : List Nat} → x ∈ (x ∷ xs)
  there : {y : Nat} {xs : List Nat} → x ∈ xs → x ∈ (y ∷ xs)

maxOfList-precond : List Nat → Set
maxOfList-precond lst = Not (lst ≡ [])

maxOfListHelper : List Nat → Nat
maxOfListHelper [] = zero
maxOfListHelper (x ∷ []) = x
maxOfListHelper (x ∷ y ∷ xs) =
  let maxTail = maxOfListHelper (y ∷ xs)
  in
    if natLess maxTail x
    then x
    else maxTail

maxOfList :
  (lst : List Nat) →
  maxOfList-precond lst →
  Nat
maxOfList lst h-precond = maxOfListHelper lst

maxOfList-postcond :
  (lst : List Nat) →
  (result : Nat) →
  maxOfList-precond lst →
  Set
maxOfList-postcond lst result h-precond =
  (result ∈ lst) ∧
  ((x : Nat) → x ∈ lst → x ≤ result)

maxOfList-spec-satisfied : Set
maxOfList-spec-satisfied =
  (lst : List Nat) →
  (h-precond : maxOfList-precond lst) →
  maxOfList-postcond
    lst
    (maxOfList lst h-precond)
    h-precond
