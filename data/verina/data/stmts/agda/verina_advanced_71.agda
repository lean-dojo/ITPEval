-- Statement-only formalization of VERINA corpus artifact verina_advanced_71,
-- catalog title "shortestBeautifulSubstring": a deterministic substring search
-- returns the shortest binary substring containing exactly k ones, breaking
-- length ties lexicographically, and is connected to its full correctness
-- contract. This file contains no proof.

{-# OPTIONS --safe #-}

module VerinaAdvanced71 where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Char using
  (Char; primCharEquality; primCharToNat)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Maybe using (Maybe; just; nothing)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.String using
  (String; primStringEquality; primStringFromList; primStringToList)

infixr 2 _∨_
infixr 3 _∧_

record Top : Set where
  constructor top

record _∧_ (A B : Set) : Set where
  constructor both
  field
    first : A
    second : B

data _∨_ (A B : Set) : Set where
  left : A → A ∨ B
  right : B → A ∨ B

data IsTrue : Bool → Set where
  true-witness : IsTrue true

if_then_else_ : {A : Set} → Bool → A → A → A
if true then when-true else when-false = when-true
if false then when-true else when-false = when-false

boolNot : Bool → Bool
boolNot true = false
boolNot false = true

boolAnd : Bool → Bool → Bool
boolAnd true value = value
boolAnd false value = false

boolOr : Bool → Bool → Bool
boolOr true value = true
boolOr false value = value

natEqual : Nat → Nat → Bool
natEqual zero zero = true
natEqual zero (suc _) = false
natEqual (suc _) zero = false
natEqual (suc m) (suc n) = natEqual m n

natLess : Nat → Nat → Bool
natLess zero zero = false
natLess zero (suc _) = true
natLess (suc _) zero = false
natLess (suc m) (suc n) = natLess m n

natSubtract : Nat → Nat → Nat
natSubtract m zero = m
natSubtract zero (suc n) = zero
natSubtract (suc m) (suc n) = natSubtract m n

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

filterList : {A : Set} → (A → Bool) → List A → List A
filterList predicate [] = []
filterList predicate (x ∷ xs) =
  if predicate x
  then x ∷ filterList predicate xs
  else filterList predicate xs

allList : {A : Set} → (A → Bool) → List A → Bool
allList predicate [] = true
allList predicate (x ∷ xs) =
  if predicate x
  then allList predicate xs
  else false

takeList : {A : Set} → Nat → List A → List A
takeList zero xs = []
takeList (suc n) [] = []
takeList (suc n) (x ∷ xs) =
  x ∷ takeList n xs

dropList : {A : Set} → Nat → List A → List A
dropList zero xs = xs
dropList (suc n) [] = []
dropList (suc n) (_ ∷ xs) = dropList n xs

rangeFrom : Nat → Nat → List Nat
rangeFrom start zero = []
rangeFrom start (suc count) =
  start ∷ rangeFrom (suc start) count

range : Nat → List Nat
range count = rangeFrom zero count

isBinaryChar : Char → Bool
isBinaryChar c =
  boolOr
    (primCharEquality c '0')
    (primCharEquality c '1')

countOnes : List Char → Nat
countOnes [] = zero
countOnes (c ∷ cs) =
  if primCharEquality c '1'
  then suc (countOnes cs)
  else countOnes cs

shortestBeautifulSubstring-precond : String → Nat → Set
shortestBeautifulSubstring-precond s k =
  IsTrue (allList isBinaryChar (primStringToList s))

charListLexLess : List Char → List Char → Bool
charListLexLess [] [] = false
charListLexLess [] (_ ∷ _) = true
charListLexLess (_ ∷ _) [] = false
charListLexLess (x ∷ xs) (y ∷ ys) =
  if natLess (primCharToNat x) (primCharToNat y)
  then true
  else
    if natEqual (primCharToNat x) (primCharToNat y)
    then charListLexLess xs ys
    else false

charListLexLessOrEqual : List Char → List Char → Bool
charListLexLessOrEqual xs ys =
  boolNot (charListLexLess ys xs)

listToString : List Char → String
listToString = primStringFromList

isLexSmaller : List Char → List Char → Bool
isLexSmaller a b = charListLexLess a b

allSubstrings : List Char → List (List Char)
allSubstrings chars =
  let n = listLength chars
  in
    flatMapList
      (λ i →
        mapList
          (λ j →
            takeList (suc j) (dropList i chars))
          (range (natSubtract n i)))
      (range n)

compareCandidates : List Char → List Char → Bool
compareCandidates a b =
  boolOr
    (natLess (listLength a) (listLength b))
    (boolAnd
      (natEqual (listLength a) (listLength b))
      (isLexSmaller a b))

foldBest :
  Maybe (List Char) →
  List (List Char) →
  Maybe (List Char)
foldBest best [] = best
foldBest nothing (current ∷ rest) =
  foldBest (just current) rest
foldBest (just best) (current ∷ rest) =
  if compareCandidates current best
  then foldBest (just current) rest
  else foldBest (just best) rest

shortestBeautifulSubstring :
  (s : String) →
  (k : Nat) →
  shortestBeautifulSubstring-precond s k →
  String
shortestBeautifulSubstring s k h-precond =
  let chars = primStringToList s
      candidates =
        filterList
          (λ substring →
            natEqual (countOnes substring) k)
          (allSubstrings chars)
      best = foldBest nothing candidates
  in resultString best
  where
  resultString : Maybe (List Char) → String
  resultString nothing = primStringFromList []
  resultString (just chars) = listToString chars

allSubstringsIncludingEmpty : List Char → List (List Char)
allSubstringsIncludingEmpty chars =
  let n = listLength chars
  in
    flatMapList
      (λ i →
        mapList
          (λ length →
            takeList length (dropList i chars))
          (range (suc (natSubtract n i))))
      (range n)

stringNotEmpty : String → Bool
stringNotEmpty s =
  boolNot (primStringEquality s (primStringFromList []))

stringMember : String → List String → Bool
stringMember sought [] = false
stringMember sought (x ∷ xs) =
  if primStringEquality sought x
  then true
  else stringMember sought xs

StringLessOrEqual : String → String → Set
StringLessOrEqual x y =
  IsTrue
    (charListLexLessOrEqual
      (primStringToList x)
      (primStringToList y))

TargetNoShorter : String → String → Set
TargetNoShorter result target =
  IsTrue
    (natLess
      (listLength (primStringToList result))
      (listLength (primStringToList target))) ∨
  ((listLength (primStringToList target) ≡
      listLength (primStringToList result)) ∧
    StringLessOrEqual result target)

AllTargetsNoShorter : String → List String → Set
AllTargetsNoShorter result [] = Top
AllTargetsNoShorter result (target ∷ targets) =
  TargetNoShorter result target ∧
  AllTargetsNoShorter result targets

shortestBeautifulSubstring-postcond :
  (s : String) →
  (k : Nat) →
  (result : String) →
  shortestBeautifulSubstring-precond s k →
  Set
shortestBeautifulSubstring-postcond s k result h-precond =
  let chars = primStringToList s
      substrings = allSubstringsIncludingEmpty chars
      beautiful =
        filterList
          (λ substring →
            natEqual (countOnes substring) k)
          substrings
      targets =
        filterList
          stringNotEmpty
          (mapList listToString beautiful)
      emptyString = primStringFromList []
  in
    ((result ≡ emptyString) ∧ (targets ≡ [])) ∨
    (IsTrue (stringMember result targets) ∧
      AllTargetsNoShorter result targets)

shortestBeautifulSubstring-spec-satisfied : Set
shortestBeautifulSubstring-spec-satisfied =
  (s : String) →
  (k : Nat) →
  (h-precond : shortestBeautifulSubstring-precond s k) →
  shortestBeautifulSubstring-postcond
    s
    k
    (shortestBeautifulSubstring s k h-precond)
    h-precond
