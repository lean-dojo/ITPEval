-- Statement-only formalization of VERINA corpus artifact verina_advanced_27,
-- catalog title "longestCommonSubsequence": a deterministic recursive string
-- program returns a longest common subsequence, characterized by exhaustive
-- subsequence enumeration. This file contains no proof.

{-# OPTIONS --safe #-}

module VerinaAdvanced27 where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Char using (Char; primCharEquality)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)
open import Agda.Builtin.String using
  (String; primStringFromList; primStringToList)

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

natLessOrEqual : Nat → Nat → Bool
natLessOrEqual zero _ = true
natLessOrEqual (suc _) zero = false
natLessOrEqual (suc m) (suc n) = natLessOrEqual m n

natGreaterOrEqual : Nat → Nat → Bool
natGreaterOrEqual m n = natLessOrEqual n m

listLength : {A : Set} → List A → Nat
listLength [] = zero
listLength (_ ∷ xs) = suc (listLength xs)

appendList : {A : Set} → List A → List A → List A
appendList [] ys = ys
appendList (x ∷ xs) ys = x ∷ appendList xs ys

mapList : {A B : Set} → (A → B) → List A → List B
mapList f [] = []
mapList f (x ∷ xs) = f x ∷ mapList f xs

filterList : {A : Set} → (A → Bool) → List A → List A
filterList predicate [] = []
filterList predicate (x ∷ xs) =
  if predicate x
  then x ∷ filterList predicate xs
  else filterList predicate xs

foldLeft : {A B : Set} → (A → B → A) → A → List B → A
foldLeft step accumulator [] = accumulator
foldLeft step accumulator (x ∷ xs) =
  foldLeft step (step accumulator x) xs

reverseOnto : {A : Set} → List A → List A → List A
reverseOnto accumulator [] = accumulator
reverseOnto accumulator (x ∷ xs) =
  reverseOnto (x ∷ accumulator) xs

reverseList : {A : Set} → List A → List A
reverseList xs = reverseOnto [] xs

allList : {A : Set} → (A → Bool) → List A → Bool
allList predicate [] = true
allList predicate (x ∷ xs) =
  if predicate x
  then allList predicate xs
  else false

listCharEqual : List Char → List Char → Bool
listCharEqual [] [] = true
listCharEqual [] (_ ∷ _) = false
listCharEqual (_ ∷ _) [] = false
listCharEqual (x ∷ xs) (y ∷ ys) =
  if primCharEquality x y
  then listCharEqual xs ys
  else false

containsCharList : List Char → List (List Char) → Bool
containsCharList sought [] = false
containsCharList sought (x ∷ xs) =
  if listCharEqual sought x
  then true
  else containsCharList sought xs

toCharList : String → List Char
toCharList s = primStringToList s

fromCharList : List Char → String
fromCharList cs = primStringFromList cs

lcsAuxFuel : Nat → List Char → List Char → List Char
lcsAuxFuel zero xs ys = []
lcsAuxFuel (suc fuel) [] ys = []
lcsAuxFuel (suc fuel) xs [] = []
lcsAuxFuel (suc fuel) (x ∷ xs) (y ∷ ys) =
  if primCharEquality x y
  then x ∷ lcsAuxFuel fuel xs ys
  else
    let left = lcsAuxFuel fuel xs (y ∷ ys)
        right = lcsAuxFuel fuel (x ∷ xs) ys
    in
      if natGreaterOrEqual (listLength left) (listLength right)
      then left
      else right

lcsAux : List Char → List Char → List Char
lcsAux xs ys =
  lcsAuxFuel (listLength xs + listLength ys) xs ys

longestCommonSubsequence-precond : String → String → Set
longestCommonSubsequence-precond s1 s2 = Top

longestCommonSubsequence :
  (s1 : String) →
  (s2 : String) →
  longestCommonSubsequence-precond s1 s2 →
  String
longestCommonSubsequence s1 s2 h-precond =
  let xs = toCharList s1
      ys = toCharList s2
      resultList = lcsAux xs ys
  in fromCharList resultList

allSubseqStep :
  List (List Char) →
  Char →
  List (List Char)
allSubseqStep accumulator x =
  appendList
    accumulator
    (mapList (λ subsequence → x ∷ subsequence) accumulator)

allSubseq : List Char → List (List Char)
allSubseq chars =
  mapList
    reverseList
    (foldLeft allSubseqStep ([] ∷ []) chars)

commonSubsequences : String → String → List (List Char)
commonSubsequences s1 s2 =
  let subseqA = allSubseq (toCharList s1)
      subseqB = allSubseq (toCharList s2)
  in
    filterList
      (λ subsequence → containsCharList subsequence subseqB)
      subseqA

longestCommonSubsequence-postcond :
  (s1 : String) →
  (s2 : String) →
  (result : String) →
  longestCommonSubsequence-precond s1 s2 →
  Set
longestCommonSubsequence-postcond s1 s2 result h-precond =
  let commonSubseq = commonSubsequences s1 s2
      resultChars = toCharList result
  in
    IsTrue (containsCharList resultChars commonSubseq) ∧
    IsTrue
      (allList
        (λ subsequence →
          natLessOrEqual
            (listLength subsequence)
            (listLength resultChars))
        commonSubseq)

longestCommonSubsequence-spec-satisfied : Set
longestCommonSubsequence-spec-satisfied =
  (s1 : String) →
  (s2 : String) →
  (h-precond : longestCommonSubsequence-precond s1 s2) →
  longestCommonSubsequence-postcond
    s1
    s2
    (longestCommonSubsequence s1 s2 h-precond)
    h-precond
