-- Statement-only formalization of VERINA corpus artifact verina_advanced_55,
-- catalog title "mostFrequent": a deterministic frequency-map program returns
-- the most frequent integer, breaking ties by first occurrence in a nonempty list.
-- This file contains no proof.

{-# OPTIONS --safe #-}

module VerinaAdvanced55 where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Int using (Int; negsuc; pos)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Maybe using (Maybe; just; nothing)
open import Agda.Builtin.Nat using (Nat; zero; suc)

infixr 3 _∧_
infix 4 _∈_

data Empty : Set where

Not : Set → Set
Not A = A → Empty

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

natLessOrEqual : Nat → Nat → Bool
natLessOrEqual zero _ = true
natLessOrEqual (suc _) zero = false
natLessOrEqual (suc m) (suc n) = natLessOrEqual m n

intEqual : Int → Int → Bool
intEqual (pos m) (pos n) = natEqual m n
intEqual (pos _) (negsuc _) = false
intEqual (negsuc _) (pos _) = false
intEqual (negsuc m) (negsuc n) = natEqual m n

foldLeft : {A B : Set} → (A → B → A) → A → List B → A
foldLeft step accumulator [] = accumulator
foldLeft step accumulator (x ∷ xs) =
  foldLeft step (step accumulator x) xs

mapList : {A B : Set} → (A → B) → List A → List B
mapList f [] = []
mapList f (x ∷ xs) = f x ∷ mapList f xs

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

containsInt : Int → List Int → Bool
containsInt sought [] = false
containsInt sought (x ∷ xs) =
  if intEqual sought x
  then true
  else containsInt sought xs

record Entry : Set where
  constructor entry
  field
    entryKey : Int
    entryValue : Nat

FrequencyTable : Set
FrequencyTable = List Entry

lookupCount : Int → FrequencyTable → Nat
lookupCount key [] = zero
lookupCount key (entry stored-key value ∷ rest) =
  if intEqual key stored-key
  then value
  else lookupCount key rest

insertCount : Int → Nat → FrequencyTable → FrequencyTable
insertCount key value [] = entry key value ∷ []
insertCount key value (entry stored-key stored-value ∷ rest) =
  if intEqual key stored-key
  then (entry key value ∷ rest)
  else (entry stored-key stored-value ∷ insertCount key value rest)

countStep : FrequencyTable → Int → FrequencyTable
countStep frequencies x =
  let current = lookupCount x frequencies
  in insertCount x (suc current) frequencies

countMap : List Int → FrequencyTable
countMap xs = foldLeft countStep [] xs

maxFrequencyStep : Nat → Entry → Nat
maxFrequencyStep accumulator (entry key value) =
  if natLess accumulator value
  then value
  else accumulator

getMaxFrequency : FrequencyTable → Nat
getMaxFrequency frequencies =
  foldLeft maxFrequencyStep zero frequencies

isTargetFrequency : Nat → Entry → Bool
isTargetFrequency maximum (entry key value) =
  natEqual value maximum

extractKey : Entry → Int
extractKey (entry key value) = key

getCandidates : FrequencyTable → Nat → List Int
getCandidates frequencies maximum =
  mapList
    extractKey
    (filterList (isTargetFrequency maximum) frequencies)

getFirstWithFreq : List Int → List Int → Int
getFirstWithFreq [] candidates = pos zero
getFirstWithFreq (x ∷ xs) candidates =
  if containsInt x candidates
  then x
  else getFirstWithFreq xs candidates

mostFrequent-precond : List Int → Set
mostFrequent-precond xs = Not (xs ≡ [])

mostFrequent :
  (xs : List Int) →
  mostFrequent-precond xs →
  Int
mostFrequent xs h-precond =
  let frequency-map = countMap xs
      maximum-frequency = getMaxFrequency frequency-map
      candidates = getCandidates frequency-map maximum-frequency
  in getFirstWithFreq xs candidates

countInt : Int → List Int → Nat
countInt sought [] = zero
countInt sought (x ∷ xs) =
  if intEqual sought x
  then suc (countInt sought xs)
  else countInt sought xs

headMaybe : {A : Set} → List A → Maybe A
headMaybe [] = nothing
headMaybe (x ∷ xs) = just x

data _∈_ (x : Int) : List Int → Set where
  here : {xs : List Int} → x ∈ (x ∷ xs)
  there : {y : Int} {xs : List Int} → x ∈ xs → x ∈ (y ∷ xs)

mostFrequent-postcond :
  (xs : List Int) →
  (result : Int) →
  mostFrequent-precond xs →
  Set
mostFrequent-postcond xs result h-precond =
  let count = λ x → countInt x xs
      maximal-elements =
        filterList
          (λ x → natEqual (count x) (count result))
          xs
  in
    result ∈ xs ∧
    IsTrue
      (allList
        (λ x → natLessOrEqual (count x) (count result))
        xs) ∧
    (headMaybe maximal-elements ≡ just result)

mostFrequent-spec-satisfied : Set
mostFrequent-spec-satisfied =
  (xs : List Int) →
  (h-precond : mostFrequent-precond xs) →
  mostFrequent-postcond
    xs
    (mostFrequent xs h-precond)
    h-precond
