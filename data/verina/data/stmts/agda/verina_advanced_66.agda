-- Statement-only formalization of VERINA corpus artifact verina_advanced_66,
-- catalog title "reverseWords": a deterministic string program removes empty
-- space-delimited chunks, reverses the remaining words, and rejoins them with
-- single spaces under its filtering-and-intercalation contract. This file
-- contains no proof.

{-# OPTIONS --safe #-}

module VerinaAdvanced66 where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Char using (Char; primCharEquality)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Sigma using (Σ)
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

if_then_else_ : {A : Set} → Bool → A → A → A
if true then when-true else when-false = when-true
if false then when-true else when-false = when-false

boolNot : Bool → Bool
boolNot true = false
boolNot false = true

mapList : {A B : Set} → (A → B) → List A → List B
mapList f [] = []
mapList f (x ∷ xs) = f x ∷ mapList f xs

filterList : {A : Set} → (A → Bool) → List A → List A
filterList predicate [] = []
filterList predicate (x ∷ xs) =
  if predicate x
  then x ∷ filterList predicate xs
  else filterList predicate xs

reverseOnto : {A : Set} → List A → List A → List A
reverseOnto [] accumulator = accumulator
reverseOnto (x ∷ xs) accumulator =
  reverseOnto xs (x ∷ accumulator)

reverseList : {A : Set} → List A → List A
reverseList xs = reverseOnto xs []

emptyString : String
emptyString = primStringFromList []

spaceString : String
spaceString = primStringFromList (' ' ∷ [])

splitOnSpaceChars :
  List Char →
  List Char →
  List (List Char)
splitOnSpaceChars current [] =
  reverseList current ∷ []
splitOnSpaceChars current (c ∷ cs) =
  if primCharEquality c ' '
  then (reverseList current ∷ splitOnSpaceChars [] cs)
  else splitOnSpaceChars (c ∷ current) cs

splitOnSpace : String → List String
splitOnSpace words-str =
  mapList
    primStringFromList
    (splitOnSpaceChars [] (primStringToList words-str))

filterNonEmpty : List String → List String
filterNonEmpty [] = []
filterNonEmpty (word ∷ words) =
  if primStringEquality word emptyString
  then filterNonEmpty words
  else (word ∷ filterNonEmpty words)

stringNotEmpty : String → Bool
stringNotEmpty word =
  boolNot (primStringEquality word emptyString)

joinWithSpace : List String → String
joinWithSpace [] = emptyString
joinWithSpace (word ∷ []) = word
joinWithSpace (word ∷ next ∷ words) =
  primStringAppend
    word
    (primStringAppend
      spaceString
      (joinWithSpace (next ∷ words)))

intercalateSpace : List String → String
intercalateSpace [] = emptyString
intercalateSpace (word ∷ []) = word
intercalateSpace (word ∷ next ∷ words) =
  primStringAppend
    word
    (primStringAppend
      spaceString
      (intercalateSpace (next ∷ words)))

reverseWords-precond : String → Set
reverseWords-precond words-str = Top

reverseWords :
  (words-str : String) →
  reverseWords-precond words-str →
  String
reverseWords words-str h-precond =
  let rawWords = splitOnSpace words-str
      filteredWords = filterNonEmpty rawWords
      revWords = reverseList filteredWords
  in joinWithSpace revWords

reverseWords-postcond :
  (words-str : String) →
  (result : String) →
  reverseWords-precond words-str →
  Set
reverseWords-postcond words-str result h-precond =
  Σ (List String) (λ words →
    (words ≡
      filterList stringNotEmpty (splitOnSpace words-str)) ∧
    (result ≡ intercalateSpace (reverseList words)))

reverseWords-spec-satisfied : Set
reverseWords-spec-satisfied =
  (words-str : String) →
  (h-precond : reverseWords-precond words-str) →
  reverseWords-postcond
    words-str
    (reverseWords words-str h-precond)
    h-precond
