-- Statement-only formalization of VERINA corpus artifact verina_advanced_76,
-- catalog title "topKFrequent": a deterministic frequency-table program
-- returns the k most frequent integers in non-increasing frequency order and
-- is connected to its full correctness contract. This file contains no proof.

{-# OPTIONS --safe #-}

module VerinaAdvanced76 where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Int using (Int; negsuc; pos)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Maybe using (Maybe; just; nothing)
open import Agda.Builtin.Nat using (Nat; zero; suc)

infixr 3 _∧_
infixr 5 _||_
infix 4 _≤_ _<_ _∈_

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

data _≤_ : Nat → Nat → Set where
  zero≤ : {n : Nat} → zero ≤ n
  suc≤suc : {m n : Nat} → m ≤ n → suc m ≤ suc n

_<_ : Nat → Nat → Set
m < n = suc m ≤ n

data IsTrue : Bool → Set where
  true-witness : IsTrue true

if_then_else_ : {A : Set} → Bool → A → A → A
if true then when-true else when-false = when-true
if false then when-true else when-false = when-false

_||_ : Bool → Bool → Bool
true || other = true
false || other = other

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

listLength : {A : Set} → List A → Nat
listLength [] = zero
listLength (_ ∷ xs) = suc (listLength xs)

appendList : {A : Set} → List A → List A → List A
appendList [] ys = ys
appendList (x ∷ xs) ys = x ∷ appendList xs ys

mapList : {A B : Set} → (A → B) → List A → List B
mapList f [] = []
mapList f (x ∷ xs) = f x ∷ mapList f xs

foldLeft : {A B : Set} → (A → B → A) → A → List B → A
foldLeft step accumulator [] = accumulator
foldLeft step accumulator (x ∷ xs) =
  foldLeft step (step accumulator x) xs

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

containsInt : Int → List Int → Bool
containsInt sought [] = false
containsInt sought (x ∷ xs) =
  if intEqual sought x
  then true
  else containsInt sought xs

eraseDups : List Int → List Int
eraseDups [] = []
eraseDups (x ∷ xs) =
  if containsInt x xs
  then eraseDups xs
  else (x ∷ eraseDups xs)

countInt : Int → List Int → Nat
countInt sought [] = zero
countInt sought (x ∷ xs) =
  if intEqual sought x
  then suc (countInt sought xs)
  else countInt sought xs

All : {A : Set} → (A → Set) → List A → Set
All predicate [] = Top
All predicate (x ∷ xs) =
  predicate x ∧ All predicate xs

Pairwise :
  {A : Set} → (A → A → Set) → List A → Set
Pairwise relation [] = Top
Pairwise relation (x ∷ xs) =
  All (relation x) xs ∧ Pairwise relation xs

data _∈_ (x : Int) : List Int → Set where
  here : {xs : List Int} → x ∈ (x ∷ xs)
  there : {y : Int} {xs : List Int} → x ∈ xs → x ∈ (y ∷ xs)

record Entry : Set where
  constructor entry
  field
    entryKey : Int
    entryCount : Nat

open Entry public

FrequencyList : Set
FrequencyList = List Entry

findEntry : Int → FrequencyList → Maybe Entry
findEntry key [] = nothing
findEntry key (current@(entry stored-key count) ∷ rest) =
  if intEqual stored-key key
  then just current
  else findEntry key rest

incrementMatching : Int → Entry → Entry
incrementMatching key (entry stored-key count) =
  if intEqual stored-key key
  then entry stored-key (suc count)
  else entry stored-key count

frequencyStep : FrequencyList → Int → FrequencyList
frequencyStep frequencies key with findEntry key frequencies
... | just current =
  mapList (incrementMatching key) frequencies
... | nothing =
  appendList frequencies (entry key (suc zero) ∷ [])

buildFrequencyList : List Int → FrequencyList
buildFrequencyList nums =
  foldLeft frequencyStep [] nums

insertSorted : Entry → FrequencyList → FrequencyList
insertSorted current [] = current ∷ []
insertSorted current@(entry key count)
  (next@(entry next-key next-count) ∷ rest) =
  if natLess next-count count
  then (current ∷ next ∷ rest)
  else (next ∷ insertSorted current rest)

sortByDescendingFrequency : FrequencyList → FrequencyList
sortByDescendingFrequency frequencies =
  foldLeft
    (λ sorted current → insertSorted current sorted)
    []
    frequencies

topKFrequent-precond : List Int → Nat → Set
topKFrequent-precond nums k =
  k ≤ listLength (eraseDups nums)

topKFrequent :
  (nums : List Int) →
  (k : Nat) →
  topKFrequent-precond nums k →
  List Int
topKFrequent nums k h-precond =
  let frequency-list = buildFrequencyList nums
      sorted = sortByDescendingFrequency frequency-list
  in mapList entryKey (takeList k sorted)

record IndexedInt : Set where
  constructor indexed
  field
    indexedValue : Int
    indexedPosition : Nat

open IndexedInt public

zipIdxFrom : Nat → List Int → List IndexedInt
zipIdxFrom position [] = []
zipIdxFrom position (x ∷ xs) =
  indexed x position ∷ zipIdxFrom (suc position) xs

zipIdx : List Int → List IndexedInt
zipIdx values = zipIdxFrom zero values

orderedByFrequency :
  List Int → IndexedInt → IndexedInt → Set
orderedByFrequency nums first-entry second-entry =
  indexedPosition first-entry < indexedPosition second-entry →
  countInt (indexedValue second-entry) nums ≤
    countInt (indexedValue first-entry) nums

topKFrequent-postcond :
  (nums : List Int) →
  (k : Nat) →
  (result : List Int) →
  topKFrequent-precond nums k →
  Set
topKFrequent-postcond nums k result h-precond =
  (listLength result ≡ k) ∧
  IsTrue
    (allList
      (λ x → containsInt x nums)
      result) ∧
  Pairwise
    (λ x y → Not (x ≡ y))
    result ∧
  IsTrue
    (allList
      (λ x →
        allList
          (λ y →
            containsInt y result ||
            natLessOrEqual
              (countInt y nums)
              (countInt x nums))
          nums)
      result) ∧
  Pairwise
    (orderedByFrequency nums)
    (zipIdx result)

topKFrequent-spec-satisfied : Set
topKFrequent-spec-satisfied =
  (nums : List Int) →
  (k : Nat) →
  (h-precond : topKFrequent-precond nums k) →
  topKFrequent-postcond
    nums
    k
    (topKFrequent nums k h-precond)
    h-precond
