-- Statement-only formalization of VERINA corpus artifact verina_advanced_35,
-- catalog title "majorityElement": a deterministic frequency-table program
-- returns the integer occurring strictly more than half the time and is
-- connected to its majority-element correctness contract. This file contains no proof.

{-# OPTIONS --safe #-}

module VerinaAdvanced35 where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Int using (Int; negsuc; pos)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Maybe using (Maybe; just; nothing)
open import Agda.Builtin.Nat using (Nat; zero; suc)

infixr 3 _∧_
infix 4 _≤_ _<_ _∈_

data Empty : Set where

Not : Set → Set
Not A = A → Empty

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

zeroInt : Int
zeroInt = pos zero

half : Nat → Nat
half zero = zero
half (suc zero) = zero
half (suc (suc n)) = suc (half n)

listLength : {A : Set} → List A → Nat
listLength [] = zero
listLength (_ ∷ xs) = suc (listLength xs)

countInt : Int → List Int → Nat
countInt sought [] = zero
countInt sought (x ∷ xs) =
  if intEqual sought x
  then suc (countInt sought xs)
  else countInt sought xs

anyMajority : List Int → List Int → Bool
anyMajority original [] = false
anyMajority original (x ∷ xs) =
  if natLess (half (listLength original)) (countInt x original)
  then true
  else anyMajority original xs

record majorityElement-precond (nums : List Int) : Set where
  constructor precondition
  field
    nonempty : zero < listLength nums
    majority-exists : IsTrue (anyMajority nums nums)

record Entry : Set where
  constructor entry
  field
    entryKey : Int
    entryCount : Nat

FrequencyTable : Set
FrequencyTable = List Entry

lookupCount : Int → FrequencyTable → Nat
lookupCount key [] = zero
lookupCount key (entry stored-key count ∷ rest) =
  if intEqual key stored-key
  then count
  else lookupCount key rest

insertCount : Int → Nat → FrequencyTable → FrequencyTable
insertCount key count [] = (entry key count) ∷ []
insertCount key count (entry stored-key stored-count ∷ rest) =
  if intEqual key stored-key
  then ((entry key count) ∷ rest)
  else ((entry stored-key stored-count) ∷ insertCount key count rest)

incrementCount : Int → FrequencyTable → FrequencyTable
incrementCount key table =
  insertCount key (suc (lookupCount key table)) table

buildCounts : List Int → FrequencyTable → FrequencyTable
buildCounts [] table = table
buildCounts (x ∷ xs) table =
  buildCounts xs (incrementCount x table)

findMajority : Nat → FrequencyTable → Maybe Int
findMajority bound [] = nothing
findMajority bound (entry key count ∷ rest) =
  if natLess bound count
  then just key
  else findMajority bound rest

majorityElement :
  (nums : List Int) →
  majorityElement-precond nums →
  Int
majorityElement nums h-precond
  with findMajority
    (half (listLength nums))
    (buildCounts nums [])
... | just key = key
... | nothing = zeroInt

data _∈_ (x : Int) : List Int → Set where
  here : {xs : List Int} → x ∈ (x ∷ xs)
  there : {y : Int} {xs : List Int} → x ∈ xs → x ∈ (y ∷ xs)

majorityElement-postcond :
  (nums : List Int) →
  (result : Int) →
  majorityElement-precond nums →
  Set
majorityElement-postcond nums result h-precond =
  (half (listLength nums) < countInt result nums) ∧
  ((x : Int) →
    x ∈ nums →
    Not (x ≡ result) →
    countInt x nums ≤ half (listLength nums))

majorityElement-spec-satisfied : Set
majorityElement-spec-satisfied =
  (nums : List Int) →
  (h-precond : majorityElement-precond nums) →
  majorityElement-postcond
    nums
    (majorityElement nums h-precond)
    h-precond
