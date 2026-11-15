-- Statement-only formalization of VERINA corpus artifact verina_basic_17,
-- catalog title "toLowercase": a deterministic string program converts ASCII
-- uppercase characters to lowercase by shifting their character codes by 32,
-- preserves all other characters, and is connected to its length-and-character
-- correctness contract. This file contains no proof.

{-# OPTIONS --safe #-}

module VerinaBasic17 where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Char using
  (Char; primCharToNat; primNatToChar)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)
open import Agda.Builtin.String using
  (String; primStringFromList; primStringToList)

infixr 3 _∧_
infix 4 _≤_ _<_
infixr 5 _&&_

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

isUpperCase : Char → Bool
isUpperCase c =
  natLessOrEqual (primCharToNat 'A') (primCharToNat c) &&
  natLessOrEqual (primCharToNat c) (primCharToNat 'Z')

shift32 : Char → Char
shift32 c = primNatToChar (primCharToNat c + 32)

lowercaseChar : Char → Char
lowercaseChar c =
  if isUpperCase c
  then shift32 c
  else c

toLowercase-precond : String → Set
toLowercase-precond s = Top

toLowercase :
  (s : String) →
  toLowercase-precond s →
  String
toLowercase s h-precond =
  primStringFromList
    (mapList lowercaseChar (primStringToList s))

toLowercase-postcond :
  (s : String) →
  (result : String) →
  toLowercase-precond s →
  Set
toLowercase-postcond s result h-precond =
  let inputChars = primStringToList s
      resultChars = primStringToList result
  in
    (listLength resultChars ≡ listLength inputChars) ∧
    ((i : Nat) →
      i < listLength inputChars →
      ((IsTrue (isUpperCase (indexDefault nullChar inputChars i)) →
        indexDefault nullChar resultChars i ≡
          shift32 (indexDefault nullChar inputChars i)) ∧
       (Not (IsTrue (isUpperCase
          (indexDefault nullChar inputChars i))) →
        indexDefault nullChar resultChars i ≡
          indexDefault nullChar inputChars i)))

toLowercase-spec-satisfied : Set
toLowercase-spec-satisfied =
  (s : String) →
  (h-precond : toLowercase-precond s) →
  toLowercase-postcond
    s
    (toLowercase s h-precond)
    h-precond
