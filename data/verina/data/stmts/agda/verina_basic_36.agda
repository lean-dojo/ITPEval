-- Statement-only formalization of VERINA corpus artifact verina_basic_36,
-- catalog title "replaceWithColon": a deterministic string program replaces
-- every space, comma, or period with a colon, preserves all other characters
-- and the string length, and is connected to its pointwise correctness
-- contract. This file contains no proof.

{-# OPTIONS --safe #-}

module VerinaBasic36 where

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

isSpaceCommaDot : Char → Bool
isSpaceCommaDot c =
  if primCharEquality c ' '
  then true
  else
    if primCharEquality c ','
    then true
    else
      if primCharEquality c '.'
      then true
      else false

replaceWithColonChar : Char → Char
replaceWithColonChar c =
  if isSpaceCommaDot c
  then ':'
  else c

replaceWithColon-precond : String → Set
replaceWithColon-precond s = Top

replaceWithColon :
  (s : String) →
  replaceWithColon-precond s →
  String
replaceWithColon s h-precond =
  primStringFromList
    (mapList replaceWithColonChar (primStringToList s))

replaceWithColon-postcond :
  (s : String) →
  (result : String) →
  replaceWithColon-precond s →
  Set
replaceWithColon-postcond s result h-precond =
  let inputChars = primStringToList s
      resultChars = primStringToList result
  in
    (listLength resultChars ≡ listLength inputChars) ∧
    ((i : Nat) →
      i < listLength inputChars →
      ((IsTrue (isSpaceCommaDot
          (indexDefault nullChar inputChars i)) →
        indexDefault nullChar resultChars i ≡ ':') ∧
       (Not (IsTrue (isSpaceCommaDot
          (indexDefault nullChar inputChars i))) →
        indexDefault nullChar resultChars i ≡
          indexDefault nullChar inputChars i)))

replaceWithColon-spec-satisfied : Set
replaceWithColon-spec-satisfied =
  (s : String) →
  (h-precond : replaceWithColon-precond s) →
  replaceWithColon-postcond
    s
    (replaceWithColon s h-precond)
    h-precond
