-- Statement-only formalization of VERINA corpus artifact verina_basic_27,
-- catalog title "findFirstRepeatedChar": a deterministic left-to-right string
-- scan returns the first character encountered for a second time and is
-- connected to its repetition-and-distinct-prefix correctness contract.
-- This file contains no proof.

{-# OPTIONS --safe #-}

module VerinaBasic27 where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Char using (Char; primCharEquality)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Maybe using (Maybe; just; nothing)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.String using (String; primStringToList)

infixr 3 _∧_
infixr 5 _&&_
infix 4 _≤_

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

if_then_else_ : {A : Set} → Bool → A → A → A
if true then when-true else when-false = when-true
if false then when-true else when-false = when-false

_&&_ : Bool → Bool → Bool
true && right = right
false && right = false

notBool : Bool → Bool
notBool true = false
notBool false = true

natEqual : Nat → Nat → Bool
natEqual zero zero = true
natEqual zero (suc _) = false
natEqual (suc _) zero = false
natEqual (suc m) (suc n) = natEqual m n

containsChar : Char → List Char → Bool
containsChar sought [] = false
containsChar sought (x ∷ xs) =
  if primCharEquality sought x
  then true
  else containsChar sought xs

findFirstRepeatedChar-loop :
  List Char →
  List Char →
  Maybe Char
findFirstRepeatedChar-loop [] seen = nothing
findFirstRepeatedChar-loop (c ∷ cs) seen =
  if containsChar c seen
  then just c
  else findFirstRepeatedChar-loop cs (c ∷ seen)

findFirstRepeatedChar-precond : String → Set
findFirstRepeatedChar-precond s = Top

findFirstRepeatedChar :
  (s : String) →
  findFirstRepeatedChar-precond s →
  Maybe Char
findFirstRepeatedChar s h-precond =
  findFirstRepeatedChar-loop (primStringToList s) []

countChar : Char → List Char → Nat
countChar sought [] = zero
countChar sought (x ∷ xs) =
  if primCharEquality sought x
  then suc (countChar sought xs)
  else countChar sought xs

takeList : {A : Set} → Nat → List A → List A
takeList zero xs = []
takeList (suc n) [] = []
takeList (suc n) (x ∷ xs) = x ∷ takeList n xs

indexOfChar : Char → List Char → Nat
indexOfChar sought [] = zero
indexOfChar sought (x ∷ xs) =
  if primCharEquality x sought
  then zero
  else suc (indexOfChar sought xs)

findDifferentIndex :
  Char →
  Nat →
  Nat →
  List Char →
  Nat
findDifferentIndex sought first-index current-index [] =
  current-index
findDifferentIndex sought first-index current-index (x ∷ xs) =
  if
    (primCharEquality x sought &&
      notBool (natEqual current-index first-index))
  then current-index
  else
    findDifferentIndex
      sought
      first-index
      (suc current-index)
      xs

secondIndex : Char → List Char → Nat
secondIndex sought xs =
  findDifferentIndex sought (indexOfChar sought xs) zero xs

All : {A : Set} → (A → Set) → List A → Set
All predicate [] = Top
All predicate (x ∷ xs) = predicate x ∧ All predicate xs

Pairwise :
  {A : Set} →
  (A → A → Set) →
  List A →
  Set
Pairwise relation [] = Top
Pairwise relation (x ∷ xs) =
  All (relation x) xs ∧ Pairwise relation xs

CharDifferent : Char → Char → Set
CharDifferent x y = Not (x ≡ y)

two : Nat
two = suc (suc zero)

findFirstRepeatedChar-postcond :
  (s : String) →
  (result : Maybe Char) →
  findFirstRepeatedChar-precond s →
  Set
findFirstRepeatedChar-postcond s (just c) h-precond =
  let chars = primStringToList s
      second-index = secondIndex c chars
  in
    (two ≤ countChar c chars) ∧
    Pairwise CharDifferent (takeList second-index chars)
findFirstRepeatedChar-postcond s nothing h-precond =
  Pairwise CharDifferent (primStringToList s)

findFirstRepeatedChar-spec-satisfied : Set
findFirstRepeatedChar-spec-satisfied =
  (s : String) →
  (h-precond : findFirstRepeatedChar-precond s) →
  findFirstRepeatedChar-postcond
    s
    (findFirstRepeatedChar s h-precond)
    h-precond
