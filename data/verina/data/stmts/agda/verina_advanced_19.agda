-- Statement-only formalization of VERINA corpus artifact verina_advanced_19,
-- catalog title "isCleanPalindrome": a deterministic string program removes
-- non-ASCII letters, lowercases ASCII uppercase letters, and tests for a palindrome.
-- This file contains no proof.

{-# OPTIONS --safe #-}

module VerinaAdvanced19 where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Char using
  (Char; primCharEquality; primCharToNat; primNatToChar)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Maybe using (Maybe; just; nothing)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)
open import Agda.Builtin.String using (String; primStringToList)

infixr 3 _∧_
infixr 5 _&&_ _||_

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

toLower : Char → Char
toLower c =
  if isUpperAlpha c
  then primNatToChar (primCharToNat c + 32)
  else c

normalizeChar : Char → Maybe Char
normalizeChar c =
  if isAlpha c
  then just (toLower c)
  else nothing

foldRight :
  {A B : Set} →
  (A → B → B) →
  B →
  List A →
  B
foldRight step base [] = base
foldRight step base (x ∷ xs) =
  step x (foldRight step base xs)

normalizeStep : Char → List Char → List Char
normalizeStep c accumulator with normalizeChar c
... | just c′ = c′ ∷ accumulator
... | nothing = accumulator

normalizeString : String → List Char
normalizeString s =
  foldRight normalizeStep [] (primStringToList s)

reverseOnto : {A : Set} → List A → List A → List A
reverseOnto accumulator [] = accumulator
reverseOnto accumulator (x ∷ xs) =
  reverseOnto (x ∷ accumulator) xs

reverseList : {A : Set} → List A → List A
reverseList xs = reverseOnto [] xs

listCharEqual : List Char → List Char → Bool
listCharEqual [] [] = true
listCharEqual [] (_ ∷ _) = false
listCharEqual (_ ∷ _) [] = false
listCharEqual (x ∷ xs) (y ∷ ys) =
  primCharEquality x y && listCharEqual xs ys

isCleanPalindrome-precond : String → Set
isCleanPalindrome-precond s = Top

isCleanPalindrome :
  (s : String) →
  isCleanPalindrome-precond s →
  Bool
isCleanPalindrome s h-precond =
  let norm = normalizeString s
  in listCharEqual norm (reverseList norm)

isCleanPalindrome-postcond :
  (s : String) →
  (result : Bool) →
  isCleanPalindrome-precond s →
  Set
isCleanPalindrome-postcond s result h-precond =
  let norm = normalizeString s
  in
    ((result ≡ true) → norm ≡ reverseList norm) ∧
    ((result ≡ false) → Not (norm ≡ reverseList norm))

isCleanPalindrome-spec-satisfied : Set
isCleanPalindrome-spec-satisfied =
  (s : String) →
  (h-precond : isCleanPalindrome-precond s) →
  isCleanPalindrome-postcond
    s
    (isCleanPalindrome s h-precond)
    h-precond
