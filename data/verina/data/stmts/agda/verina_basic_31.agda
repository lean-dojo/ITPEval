-- Statement-only formalization of VERINA corpus artifact verina_basic_31,
-- catalog title "toUppercase": a deterministic string program converts ASCII
-- lowercase letters to uppercase by the specified code-point shift, preserves
-- all other characters and the string length, and is connected to its
-- pointwise correctness contract. This file contains no proof.

{-# OPTIONS --safe #-}

module VerinaBasic31 where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Char using
  (Char; primCharToNat; primNatToChar)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc; mod-helper)
open import Agda.Builtin.String using
  (String; primStringFromList; primStringToList)

infixr 3 _∧_
infixr 5 _&&_
infix 4 _≤_ _<_

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

data _≤_ : Nat → Nat → Set where
  zero≤ : {n : Nat} → zero ≤ n
  suc≤suc : {m n : Nat} → m ≤ n → suc m ≤ suc n

_<_ : Nat → Nat → Set
m < n = suc m ≤ n

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

natSubtract : Nat → Nat → Nat
natSubtract m zero = m
natSubtract zero (suc n) = zero
natSubtract (suc m) (suc n) = natSubtract m n

naturalMod : Nat → Nat → Nat
naturalMod numerator zero = numerator
naturalMod numerator (suc denominator) =
  mod-helper zero denominator numerator denominator

listLength : {A : Set} → List A → Nat
listLength [] = zero
listLength (_ ∷ xs) = suc (listLength xs)

indexDefault : {A : Set} → A → List A → Nat → A
indexDefault default [] index = default
indexDefault default (x ∷ xs) zero = x
indexDefault default (x ∷ xs) (suc index) =
  indexDefault default xs index

mapList : {A B : Set} → (A → B) → List A → List B
mapList function [] = []
mapList function (x ∷ xs) =
  function x ∷ mapList function xs

nullChar : Char
nullChar = primNatToChar zero

isLowerCase : Char → Bool
isLowerCase c =
  natLessOrEqual 97 (primCharToNat c) &&
  natLessOrEqual (primCharToNat c) 122

shiftMinus32 : Char → Char
shiftMinus32 c =
  primNatToChar
    (naturalMod
      (natSubtract (primCharToNat c) 32)
      128)

toUppercase-precond : String → Set
toUppercase-precond s = Top

toUppercase :
  (s : String) →
  toUppercase-precond s →
  String
toUppercase s h-precond =
  primStringFromList
    (mapList
      (λ c →
        if isLowerCase c
        then shiftMinus32 c
        else c)
      (primStringToList s))

toUppercase-postcond :
  (s : String) →
  (result : String) →
  toUppercase-precond s →
  Set
toUppercase-postcond s result h-precond =
  let inputChars = primStringToList s
      resultChars = primStringToList result
  in
    (listLength resultChars ≡ listLength inputChars) ∧
    ((i : Nat) →
      i < listLength inputChars →
      ((IsTrue (isLowerCase (indexDefault nullChar inputChars i)) →
        indexDefault nullChar resultChars i ≡
          shiftMinus32 (indexDefault nullChar inputChars i)) ∧
       (Not (IsTrue (isLowerCase (indexDefault nullChar inputChars i))) →
        indexDefault nullChar resultChars i ≡
          indexDefault nullChar inputChars i)))

toUppercase-spec-satisfied : Set
toUppercase-spec-satisfied =
  (s : String) →
  (h-precond : toUppercase-precond s) →
  toUppercase-postcond
    s
    (toUppercase s h-precond)
    h-precond
