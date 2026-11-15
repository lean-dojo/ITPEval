-- Statement-only formalization of VERINA corpus artifact verina_advanced_59,
-- catalog title "palindromeIgnoreNonAlnum": a deterministic string program
-- filters non-alphanumeric characters, lowercases letters, and checks whether
-- the resulting character list is a palindrome. This file contains no proof.

{-# OPTIONS --safe #-}

module VerinaAdvanced59 where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Char using
  (Char; primCharEquality; primCharToNat; primNatToChar)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Maybe using (Maybe; just; nothing)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)
open import Agda.Builtin.String using (String; primStringToList)

infixr 5 _&&_ _||_

data Empty : Set where

Not : Set → Set
Not A = A → Empty

record Top : Set where
  constructor top

if_then_else_ : {A : Set} → Bool → A → A → A
if true then when-true else when-false = when-true
if false then when-true else when-false = when-false

_&&_ : Bool → Bool → Bool
true && other = other
false && other = false

_||_ : Bool → Bool → Bool
true || other = true
false || other = other

natLessOrEqual : Nat → Nat → Bool
natLessOrEqual zero _ = true
natLessOrEqual (suc _) zero = false
natLessOrEqual (suc m) (suc n) = natLessOrEqual m n

natGreaterOrEqual : Nat → Nat → Bool
natGreaterOrEqual m n = natLessOrEqual n m

isUpperAlpha : Char → Bool
isUpperAlpha c =
  natLessOrEqual 65 (primCharToNat c) &&
  natLessOrEqual (primCharToNat c) 90

isLowerAlpha : Char → Bool
isLowerAlpha c =
  natLessOrEqual 97 (primCharToNat c) &&
  natLessOrEqual (primCharToNat c) 122

isAlpha : Char → Bool
isAlpha c = isUpperAlpha c || isLowerAlpha c

isDigit : Char → Bool
isDigit c =
  natLessOrEqual 48 (primCharToNat c) &&
  natLessOrEqual (primCharToNat c) 57

isAlphanumeric : Char → Bool
isAlphanumeric c = isAlpha c || isDigit c

toLower : Char → Char
toLower c =
  if isUpperAlpha c
  then primNatToChar (primCharToNat c + 32)
  else c

filterList :
  {A : Set} →
  (A → Bool) →
  List A →
  List A
filterList predicate [] = []
filterList predicate (x ∷ xs) =
  if predicate x
  then x ∷ filterList predicate xs
  else filterList predicate xs

mapList :
  {A B : Set} →
  (A → B) →
  List A →
  List B
mapList function [] = []
mapList function (x ∷ xs) =
  function x ∷ mapList function xs

cleanString : String → List Char
cleanString s =
  mapList
    toLower
    (filterList isAlphanumeric (primStringToList s))

listLength : {A : Set} → List A → Nat
listLength [] = zero
listLength (_ ∷ xs) = suc (listLength xs)

predecessor : Nat → Nat
predecessor zero = zero
predecessor (suc n) = n

listIndex : {A : Set} → Nat → List A → Maybe A
listIndex zero [] = nothing
listIndex zero (x ∷ xs) = just x
listIndex (suc n) [] = nothing
listIndex (suc n) (_ ∷ xs) = listIndex n xs

maybeCharEqual : Maybe Char → Maybe Char → Bool
maybeCharEqual nothing nothing = true
maybeCharEqual nothing (just _) = false
maybeCharEqual (just _) nothing = false
maybeCharEqual (just x) (just y) = primCharEquality x y

charactersEqualAt :
  Nat →
  Nat →
  List Char →
  Bool
charactersEqualAt left right chars =
  maybeCharEqual
    (listIndex left chars)
    (listIndex right chars)

checkIndices :
  Nat →
  Nat →
  List Char →
  Bool
checkIndices left zero chars = true
checkIndices left (suc right) chars =
  if natGreaterOrEqual left (suc right)
  then true
  else
    if charactersEqualAt left (suc right) chars
    then checkIndices (suc left) right chars
    else false

reverseOnto : {A : Set} → List A → List A → List A
reverseOnto accumulator [] = accumulator
reverseOnto accumulator (x ∷ xs) =
  reverseOnto (x ∷ accumulator) xs

reverseList : {A : Set} → List A → List A
reverseList xs = reverseOnto [] xs

chooseSet : Bool → Set → Set → Set
chooseSet true when-true when-false = when-true
chooseSet false when-true when-false = when-false

palindromeIgnoreNonAlnum-precond : String → Set
palindromeIgnoreNonAlnum-precond s = Top

palindromeIgnoreNonAlnum :
  (s : String) →
  palindromeIgnoreNonAlnum-precond s →
  Bool
palindromeIgnoreNonAlnum s h-precond =
  let cleaned = cleanString s
      n = listLength cleaned
      start-index = zero
      end-index = predecessor n
  in checkIndices start-index end-index cleaned

palindromeIgnoreNonAlnum-postcond :
  (s : String) →
  (result : Bool) →
  palindromeIgnoreNonAlnum-precond s →
  Set
palindromeIgnoreNonAlnum-postcond s result h-precond =
  let cleaned = cleanString s
      forward = cleaned
      backward = reverseList cleaned
  in
    chooseSet
      result
      (forward ≡ backward)
      (Not (forward ≡ backward))

palindromeIgnoreNonAlnum-spec-satisfied : Set
palindromeIgnoreNonAlnum-spec-satisfied =
  (s : String) →
  (h-precond : palindromeIgnoreNonAlnum-precond s) →
  palindromeIgnoreNonAlnum-postcond
    s
    (palindromeIgnoreNonAlnum s h-precond)
    h-precond
