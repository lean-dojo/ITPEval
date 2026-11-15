-- Statement-only formalization of VERINA corpus artifact verina_basic_16,
-- catalog title "replaceChars": a deterministic string program replaces every
-- occurrence of one character with another while preserving the string length
-- and all nonmatching characters. This file contains no proof.

{-# OPTIONS --safe #-}

module VerinaBasic16 where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Char using
  (Char; primCharEquality; primNatToChar)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.String using
  (String; primStringFromList; primStringToList)

infixr 3 _∧_
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

data _≤_ : Nat → Nat → Set where
  zero≤ : {n : Nat} → zero ≤ n
  suc≤suc : {m n : Nat} → m ≤ n → suc m ≤ suc n

_<_ : Nat → Nat → Set
m < n = suc m ≤ n

if_then_else_ : {A : Set} → Bool → A → A → A
if true then when-true else when-false = when-true
if false then when-true else when-false = when-false

listLength : {A : Set} → List A → Nat
listLength [] = zero
listLength (_ ∷ xs) = suc (listLength xs)

indexDefault : {A : Set} → A → List A → Nat → A
indexDefault default [] index = default
indexDefault default (x ∷ xs) zero = x
indexDefault default (x ∷ xs) (suc index) =
  indexDefault default xs index

mapList : {A B : Set} → (A → B) → List A → List B
mapList f [] = []
mapList f (x ∷ xs) = f x ∷ mapList f xs

nullChar : Char
nullChar = primNatToChar zero

replaceChar : Char → Char → Char → Char
replaceChar oldChar newChar c =
  if primCharEquality c oldChar
  then newChar
  else c

replaceChars-precond : String → Char → Char → Set
replaceChars-precond s oldChar newChar = Top

replaceChars :
  (s : String) →
  (oldChar newChar : Char) →
  replaceChars-precond s oldChar newChar →
  String
replaceChars s oldChar newChar h-precond =
  primStringFromList
    (mapList
      (replaceChar oldChar newChar)
      (primStringToList s))

replaceChars-postcond :
  (s : String) →
  (oldChar newChar : Char) →
  (result : String) →
  replaceChars-precond s oldChar newChar →
  Set
replaceChars-postcond s oldChar newChar result h-precond =
  let inputChars = primStringToList s
      resultChars = primStringToList result
  in
    (listLength resultChars ≡ listLength inputChars) ∧
    ((i : Nat) →
      i < listLength inputChars →
      ((indexDefault nullChar inputChars i ≡ oldChar →
        indexDefault nullChar resultChars i ≡ newChar) ∧
       (Not (indexDefault nullChar inputChars i ≡ oldChar) →
        indexDefault nullChar resultChars i ≡
          indexDefault nullChar inputChars i)))

replaceChars-spec-satisfied : Set
replaceChars-spec-satisfied =
  (s : String) →
  (oldChar newChar : Char) →
  (h-precond : replaceChars-precond s oldChar newChar) →
  replaceChars-postcond
    s
    oldChar
    newChar
    (replaceChars s oldChar newChar h-precond)
    h-precond
