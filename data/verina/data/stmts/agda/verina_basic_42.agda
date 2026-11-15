-- Statement-only formalization of VERINA corpus artifact verina_basic_42,
-- catalog title "countDigits": a deterministic string program counts
-- characters in the inclusive range '0' through '9' and is connected to its
-- two-sided truncated-subtraction correctness contract. This file contains no proof.

{-# OPTIONS --safe #-}

module VerinaBasic42 where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Char using (Char; primCharToNat)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.String using (String; primStringToList)

infixr 3 _∧_
infixr 5 _&&_

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

_&&_ : Bool → Bool → Bool
true && other = other
false && other = false

natLessOrEqual : Nat → Nat → Bool
natLessOrEqual zero _ = true
natLessOrEqual (suc _) zero = false
natLessOrEqual (suc m) (suc n) = natLessOrEqual m n

isDigit : Char → Bool
isDigit c =
  natLessOrEqual (primCharToNat '0') (primCharToNat c) &&
  natLessOrEqual (primCharToNat c) (primCharToNat '9')

filterList : {A : Set} → (A → Bool) → List A → List A
filterList predicate [] = []
filterList predicate (x ∷ xs) =
  if predicate x
  then x ∷ filterList predicate xs
  else filterList predicate xs

listLength : {A : Set} → List A → Nat
listLength [] = zero
listLength (_ ∷ xs) = suc (listLength xs)

natSubtract : Nat → Nat → Nat
natSubtract m zero = m
natSubtract zero (suc n) = zero
natSubtract (suc m) (suc n) = natSubtract m n

digitCount : String → Nat
digitCount s =
  listLength
    (filterList isDigit (primStringToList s))

countDigits-precond : String → Set
countDigits-precond s = Top

countDigits :
  (s : String) →
  countDigits-precond s →
  Nat
countDigits s h-precond = digitCount s

countDigits-postcond :
  (s : String) →
  (result : Nat) →
  countDigits-precond s →
  Set
countDigits-postcond s result h-precond =
  (natSubtract result (digitCount s) ≡ zero) ∧
  (natSubtract (digitCount s) result ≡ zero)

countDigits-spec-satisfied : Set
countDigits-spec-satisfied =
  (s : String) →
  (h-precond : countDigits-precond s) →
  countDigits-postcond
    s
    (countDigits s h-precond)
    h-precond
