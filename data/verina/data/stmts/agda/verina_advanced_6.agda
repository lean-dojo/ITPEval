-- Statement-only formalization of VERINA corpus artifact verina_advanced_6,
-- catalog title "allVowels": a deterministic case-insensitive string program
-- decides whether all five English vowels occur. This file contains no proof.

{-# OPTIONS --safe #-}

module VerinaAdvanced6 where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Char using
  (Char; primCharEquality; primCharToNat; primNatToChar)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)
open import Agda.Builtin.String using (String; primStringToList)

infix 2 _↔_
infixr 5 _&&_

record Top : Set where
  constructor top

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

toLower : Char → Char
toLower c =
  if
    natLessOrEqual (primCharToNat 'A') (primCharToNat c) &&
    natLessOrEqual (primCharToNat c) (primCharToNat 'Z')
  then primNatToChar (primCharToNat c + 32)
  else c

mapList : {A B : Set} → (A → B) → List A → List B
mapList f [] = []
mapList f (x ∷ xs) = f x ∷ mapList f xs

normalize-str : String → List Char
normalize-str s = mapList toLower (primStringToList s)

containsChar : Char → List Char → Bool
containsChar sought [] = false
containsChar sought (x ∷ xs) =
  if primCharEquality sought x
  then true
  else containsChar sought xs

allList : {A : Set} → (A → Bool) → List A → Bool
allList predicate [] = true
allList predicate (x ∷ xs) =
  if predicate x
  then allList predicate xs
  else false

vowelSet : List Char
vowelSet = 'a' ∷ 'e' ∷ 'i' ∷ 'o' ∷ 'u' ∷ []

allVowels-precond : String → Set
allVowels-precond s = Top

allVowels :
  (s : String) →
  allVowels-precond s →
  Bool
allVowels s h-precond =
  let chars = normalize-str s
  in allList (λ v → containsChar v chars) vowelSet

allVowels-postcond :
  (s : String) →
  (result : Bool) →
  allVowels-precond s →
  Set
allVowels-postcond s result h-precond =
  let chars = normalize-str s
  in
    IsTrue result ↔
    IsTrue (allList (λ v → containsChar v chars) vowelSet)

allVowels-spec-satisfied : Set
allVowels-spec-satisfied =
  (s : String) →
  (h-precond : allVowels-precond s) →
  allVowels-postcond
    s
    (allVowels s h-precond)
    h-precond
