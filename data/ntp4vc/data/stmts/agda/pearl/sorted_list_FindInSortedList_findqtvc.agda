-- Statement-only formalization of the NTP4VC corpus artifact
-- pearl/sorted_list_FindInSortedList_findqtvc: the verification condition for
-- Boolean membership search in a sorted list of integers. This file contains
-- no proof.

{-# OPTIONS --safe #-}

module sorted_list_FindInSortedList_findqtvc where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Int using (Int; negsuc; pos)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc)

infix 4 _≤Z_ _<Z_ _∈_
infixr 3 _∧_
infix 2 _↔_

data ⊤ : Set where
  tt : ⊤

data ⊥ : Set where

Not : Set → Set
Not A = A → ⊥

record _∧_ (A B : Set) : Set where
  constructor both
  field
    first  : A
    second : B

record _↔_ (A B : Set) : Set where
  constructor iff
  field
    forward  : A → B
    backward : B → A

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

intLess : Int → Int → Bool
intLess (pos m) (pos n) = natLess m n
intLess (pos _) (negsuc _) = false
intLess (negsuc _) (pos _) = true
intLess (negsuc m) (negsuc n) = natLess n m

intLessOrEqual : Int → Int → Bool
intLessOrEqual (pos m) (pos n) = natLessOrEqual m n
intLessOrEqual (pos _) (negsuc _) = false
intLessOrEqual (negsuc _) (pos _) = true
intLessOrEqual (negsuc m) (negsuc n) = natLessOrEqual n m

_≤Z_ : Int → Int → Set
x ≤Z y = intLessOrEqual x y ≡ true

_<Z_ : Int → Int → Set
x <Z y = intLess x y ≡ true

data _∈_ {A : Set} (x : A) : List A → Set where
  here :
    {xs : List A} →
    x ∈ (x ∷ xs)

  there :
    {y : A} {xs : List A} →
    x ∈ xs →
    x ∈ (y ∷ xs)

memberBool : Int → List Int → Bool
memberBool x [] = false
memberBool x (y ∷ ys) with intEqual x y
... | true = true
... | false = memberBool x ys

data Sorted : List Int → Set where
  sortedNil :
    Sorted []

  sortedOne :
    (x : Int) →
    Sorted (x ∷ [])

  sortedTwo :
    (x y : Int) →
    (xs : List Int) →
    x ≤Z y →
    Sorted (y ∷ xs) →
    Sorted (x ∷ y ∷ xs)

TailMatches : List Int → List Int → Set
TailMatches [] expected = ⊥
TailMatches (_ ∷ actual) expected = actual ≡ expected

InitialObligation : List Int → Int → Set
InitialObligation [] x = ⊤
InitialObligation whole@(y ∷ r) x =
  Not (x ≡ y) →
  y <Z x →
  TailMatches whole r ∧ Sorted r

ResultPremise : List Int → Int → Bool → Set
ResultPremise [] x result = result ≡ false
ResultPremise (y ∷ r) x result with intEqual x y
... | true = result ≡ true
... | false with intLess y x
...   | true = result ≡ memberBool x r
...   | false = result ≡ false

ResultCorrect : List Int → Int → Bool → Set
ResultCorrect l x result =
  (result ≡ true) ↔ (x ∈ l)

find'vc : Set
find'vc =
  (l : List Int) →
  (x : Int) →
  Sorted l →
  InitialObligation l x ∧
  ((result : Bool) →
    ResultPremise l x result →
    ResultCorrect l x result)
