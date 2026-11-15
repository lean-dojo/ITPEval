-- Statement-only formalization of VERINA corpus artifact verina_advanced_60,
-- catalog title "partitionEvensOdds": a deterministic list program stably
-- partitions natural numbers into even and odd sublists and is connected to
-- its filtering and parity-classification contract. This file contains no proof.

{-# OPTIONS --safe #-}

module VerinaAdvanced60 where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc; mod-helper)

infixr 3 _∧_

record Top : Set where
  constructor top

record _∧_ (A B : Set) : Set where
  constructor both
  field
    first : A
    second : B

if_then_else_ : {A : Set} → Bool → A → A → A
if true then when-true else when-false = when-true
if false then when-true else when-false = when-false

natEqual : Nat → Nat → Bool
natEqual zero zero = true
natEqual zero (suc _) = false
natEqual (suc _) zero = false
natEqual (suc m) (suc n) = natEqual m n

naturalMod : Nat → Nat → Nat
naturalMod numerator zero = numerator
naturalMod numerator (suc denominator) =
  mod-helper zero denominator numerator denominator

one : Nat
one = suc zero

two : Nat
two = suc one

record NatListPair : Set where
  constructor pair
  field
    pairFirst : List Nat
    pairSecond : List Nat

open NatListPair public

appendList : {A : Set} → List A → List A → List A
appendList [] ys = ys
appendList (x ∷ xs) ys = x ∷ appendList xs ys

filterList : {A : Set} → (A → Bool) → List A → List A
filterList predicate [] = []
filterList predicate (x ∷ xs) =
  if predicate x
  then x ∷ filterList predicate xs
  else filterList predicate xs

allList : {A : Set} → (A → Bool) → List A → Bool
allList predicate [] = true
allList predicate (x ∷ xs) =
  if predicate x
  then allList predicate xs
  else false

isEven : Nat → Bool
isEven n = natEqual (naturalMod n two) zero

isOdd : Nat → Bool
isOdd n = natEqual (naturalMod n two) one

partitionEvensOdds-precond : List Nat → Set
partitionEvensOdds-precond nums = Top

partitionEvensOdds-helper : List Nat → NatListPair
partitionEvensOdds-helper [] = pair [] []
partitionEvensOdds-helper (x ∷ xs) =
  let rest = partitionEvensOdds-helper xs
  in
    if isEven x
    then pair (x ∷ pairFirst rest) (pairSecond rest)
    else pair (pairFirst rest) (x ∷ pairSecond rest)

partitionEvensOdds :
  (nums : List Nat) →
  partitionEvensOdds-precond nums →
  NatListPair
partitionEvensOdds nums h-precond =
  partitionEvensOdds-helper nums

partitionEvensOdds-postcond :
  (nums : List Nat) →
  (result : NatListPair) →
  partitionEvensOdds-precond nums →
  Set
partitionEvensOdds-postcond nums result h-precond =
  (appendList (pairFirst result) (pairSecond result) ≡
   appendList
     (filterList isEven nums)
     (filterList isOdd nums)) ∧
  (allList isEven (pairFirst result) ≡ true) ∧
  (allList isOdd (pairSecond result) ≡ true)

partitionEvensOdds-spec-satisfied : Set
partitionEvensOdds-spec-satisfied =
  (nums : List Nat) →
  (h-precond : partitionEvensOdds-precond nums) →
  partitionEvensOdds-postcond
    nums
    (partitionEvensOdds nums h-precond)
    h-precond
