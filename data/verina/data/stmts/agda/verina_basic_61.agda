-- Statement-only formalization of VERINA corpus artifact verina_basic_61,
-- catalog title "allDigits": a deterministic string scan returns true exactly
-- when every character lies between '0' and '9', and is connected to its
-- no-precondition correctness contract. This file contains no proof.

{-# OPTIONS --safe #-}

module VerinaBasic61 where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Char using (Char; primCharToNat)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.String using (String; primStringToList)

infix 2 _↔_
infixr 3 _∧_
infixr 5 _&&_

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

data IsTrue : Bool → Set where
  true-witness : IsTrue true

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

allDigits-precond : String → Set
allDigits-precond s = Top

allDigits-loop : List Char → Bool
allDigits-loop [] = true
allDigits-loop (c ∷ cs) =
  if isDigit c
  then allDigits-loop cs
  else false

allDigits :
  (s : String) →
  allDigits-precond s →
  Bool
allDigits s h-precond =
  allDigits-loop (primStringToList s)

AllDigitChars : List Char → Set
AllDigitChars [] = Top
AllDigitChars (c ∷ cs) =
  IsTrue (isDigit c) ∧ AllDigitChars cs

allDigits-postcond :
  (s : String) →
  (result : Bool) →
  allDigits-precond s →
  Set
allDigits-postcond s result h-precond =
  IsTrue result ↔ AllDigitChars (primStringToList s)

allDigits-spec-satisfied : Set
allDigits-spec-satisfied =
  (s : String) →
  (h-precond : allDigits-precond s) →
  allDigits-postcond
    s
    (allDigits s h-precond)
    h-precond
