-- Statement-only formalization of VERINA corpus artifact verina_advanced_26,
-- catalog title "letterCombinations": a deterministic recursive string program
-- generates telephone-keypad letter combinations, with empty or invalid input
-- producing the empty list. This file contains no proof.

{-# OPTIONS --safe #-}

module VerinaAdvanced26 where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Char using (Char; primCharEquality)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.String using
  (String; primStringAppend; primStringEquality; primStringFromList;
   primStringToList)

infixr 3 _∧_

record Top : Set where
  constructor top

record _∧_ (A B : Set) : Set where
  constructor both
  field
    first : A
    second : B

data IsTrue : Bool → Set where
  true-witness : IsTrue true

if_then_else_ : {A : Set} → Bool → A → A → A
if true then when-true else when-false = when-true
if false then when-true else when-false = when-false

notBool : Bool → Bool
notBool true = false
notBool false = true

listIsEmpty : {A : Set} → List A → Bool
listIsEmpty [] = true
listIsEmpty (_ ∷ _) = false

listLength : {A : Set} → List A → Nat
listLength [] = zero
listLength (_ ∷ xs) = suc (listLength xs)

appendList : {A : Set} → List A → List A → List A
appendList [] ys = ys
appendList (x ∷ xs) ys = x ∷ appendList xs ys

mapList : {A B : Set} → (A → B) → List A → List B
mapList f [] = []
mapList f (x ∷ xs) = f x ∷ mapList f xs

flatMapList : {A B : Set} → (A → List B) → List A → List B
flatMapList f [] = []
flatMapList f (x ∷ xs) =
  appendList (f x) (flatMapList f xs)

foldLeft : {A B : Set} → (A → B → A) → A → List B → A
foldLeft step accumulator [] = accumulator
foldLeft step accumulator (x ∷ xs) =
  foldLeft step (step accumulator x) xs

anyList : {A : Set} → (A → Bool) → List A → Bool
anyList predicate [] = false
anyList predicate (x ∷ xs) =
  if predicate x
  then true
  else anyList predicate xs

allList : {A : Set} → (A → Bool) → List A → Bool
allList predicate [] = true
allList predicate (x ∷ xs) =
  if predicate x
  then allList predicate xs
  else false

containsChar : Char → List Char → Bool
containsChar sought [] = false
containsChar sought (x ∷ xs) =
  if primCharEquality sought x
  then true
  else containsChar sought xs

containsString : String → List String → Bool
containsString sought [] = false
containsString sought (x ∷ xs) =
  if primStringEquality sought x
  then true
  else containsString sought xs

digitToLetters : Char → List Char
digitToLetters c =
  if primCharEquality c '2' then 'a' ∷ 'b' ∷ 'c' ∷ [] else
  if primCharEquality c '3' then 'd' ∷ 'e' ∷ 'f' ∷ [] else
  if primCharEquality c '4' then 'g' ∷ 'h' ∷ 'i' ∷ [] else
  if primCharEquality c '5' then 'j' ∷ 'k' ∷ 'l' ∷ [] else
  if primCharEquality c '6' then 'm' ∷ 'n' ∷ 'o' ∷ [] else
  if primCharEquality c '7' then 'p' ∷ 'q' ∷ 'r' ∷ 's' ∷ [] else
  if primCharEquality c '8' then 't' ∷ 'u' ∷ 'v' ∷ [] else
  if primCharEquality c '9' then 'w' ∷ 'x' ∷ 'y' ∷ 'z' ∷ [] else
  []

validDigits : List Char
validDigits =
  '2' ∷ '3' ∷ '4' ∷ '5' ∷ '6' ∷ '7' ∷ '8' ∷ '9' ∷ []

singletonString : Char → String
singletonString c = primStringFromList (c ∷ [])

letterCombinations-precond : String → Set
letterCombinations-precond digits = Top

prependCurrentLetters :
  List Char →
  List String →
  List String
prependCurrentLetters currentLetters [] =
  mapList singletonString currentLetters
prependCurrentLetters currentLetters rest@(_ ∷ _) =
  flatMapList
    (λ c →
      mapList
        (λ s → primStringAppend (singletonString c) s)
        rest)
    currentLetters

letterCombinationsGo : List Char → List String
letterCombinationsGo [] = []
letterCombinationsGo (d ∷ ds) =
  prependCurrentLetters
    (digitToLetters d)
    (letterCombinationsGo ds)

letterCombinations :
  (digits : String) →
  letterCombinations-precond digits →
  List String
letterCombinations digits h-precond =
  let chars = primStringToList digits
  in
    if anyList (λ c → listIsEmpty (digitToLetters c)) chars
    then []
    else letterCombinationsGo chars

expectedStep :
  List String →
  List Char →
  List String
expectedStep accumulator letters =
  flatMapList
    (λ s →
      mapList
        (λ c → primStringAppend s (singletonString c))
        letters)
    accumulator

expectedCombinations : String → List String
expectedCombinations digits =
  foldLeft
    expectedStep
    (primStringFromList [] ∷ [])
    (mapList digitToLetters (primStringToList digits))

letterCombinations-postcond :
  (digits : String) →
  (result : List String) →
  letterCombinations-precond digits →
  Set
letterCombinations-postcond digits result h-precond
  with listIsEmpty (primStringToList digits)
... | true = result ≡ []
... | false
  with anyList
    (λ c → notBool (containsChar c validDigits))
    (primStringToList digits)
... | true = result ≡ []
... | false =
  let expected = expectedCombinations digits
  in
    (listLength result ≡ listLength expected) ∧
    IsTrue (allList (λ s → containsString s expected) result) ∧
    IsTrue (allList (λ s → containsString s result) expected)

letterCombinations-spec-satisfied : Set
letterCombinations-spec-satisfied =
  (digits : String) →
  (h-precond : letterCombinations-precond digits) →
  letterCombinations-postcond
    digits
    (letterCombinations digits h-precond)
    h-precond
