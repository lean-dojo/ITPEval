-- Statement-only formalization of VERINA corpus artifact verina_basic_22,
-- catalog title "dissimilarElements": a deterministic integer-array program
-- computes the sorted duplicate-free symmetric difference and is connected to
-- its full membership, ordering, uniqueness, and coverage contract. This file
-- contains no proof.

{-# OPTIONS --safe #-}

module VerinaBasic22 where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Int using (Int; negsuc; pos)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc)

infixr 3 _∧_
infix 4 _∈_

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

if_then_else_ : {A : Set} → Bool → A → A → A
if true then when-true else when-false = when-true
if false then when-true else when-false = when-false

chooseSet : Bool → Set → Set → Set
chooseSet true when-true when-false = when-true
chooseSet false when-true when-false = when-false

notBool : Bool → Bool
notBool true = false
notBool false = true

natEqual : Nat → Nat → Bool
natEqual zero zero = true
natEqual zero (suc _) = false
natEqual (suc _) zero = false
natEqual (suc m) (suc n) = natEqual m n

natLessOrEqual : Nat → Nat → Bool
natLessOrEqual zero _ = true
natLessOrEqual (suc _) zero = false
natLessOrEqual (suc m) (suc n) = natLessOrEqual m n

intEqual : Int → Int → Bool
intEqual (pos m) (pos n) = natEqual m n
intEqual (pos _) (negsuc _) = false
intEqual (negsuc _) (pos _) = false
intEqual (negsuc m) (negsuc n) = natEqual m n

intLessOrEqual : Int → Int → Bool
intLessOrEqual (pos m) (pos n) = natLessOrEqual m n
intLessOrEqual (pos _) (negsuc _) = false
intLessOrEqual (negsuc _) (pos _) = true
intLessOrEqual (negsuc m) (negsuc n) = natLessOrEqual n m

data IsTrue : Bool → Set where
  true-witness : IsTrue true

IntLessOrEqual : Int → Int → Set
IntLessOrEqual x y = IsTrue (intLessOrEqual x y)

Array : Set → Set
Array A = List A

inArray : Array Int → Int → Bool
inArray [] sought = false
inArray (x ∷ xs) sought =
  if intEqual x sought
  then true
  else inArray xs sought

foldLeft : {A B : Set} → (A → B → A) → A → List B → A
foldLeft step accumulator [] = accumulator
foldLeft step accumulator (x ∷ xs) =
  foldLeft step (step accumulator x) xs

insertDistinct : List Int → Int → List Int
insertDistinct accumulator x =
  if inArray accumulator x
  then accumulator
  else (x ∷ accumulator)

dissimilarStep : Array Int → List Int → Int → List Int
dissimilarStep excluded accumulator x =
  if notBool (inArray excluded x)
  then insertDistinct accumulator x
  else accumulator

insertSorted : Int → List Int → List Int
insertSorted x [] = x ∷ []
insertSorted x (y ∷ ys) =
  if intLessOrEqual x y
  then (x ∷ y ∷ ys)
  else (y ∷ insertSorted x ys)

sortList : List Int → List Int
sortList [] = []
sortList (x ∷ xs) = insertSorted x (sortList xs)

dissimilarElements-precond :
  Array Int → Array Int → Set
dissimilarElements-precond a b = Top

dissimilarElements :
  (a b : Array Int) →
  dissimilarElements-precond a b →
  Array Int
dissimilarElements a b h-precond =
  sortList
    (foldLeft
      (dissimilarStep a)
      (foldLeft (dissimilarStep b) [] a)
      b)

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
  there :
    {y : Int} {xs : List Int} →
    x ∈ xs →
    x ∈ (y ∷ xs)

NoDuplicates : List Int → Set
NoDuplicates [] = Top
NoDuplicates (x ∷ xs) =
  Not (x ∈ xs) ∧ NoDuplicates xs

dissimilarElements-postcond :
  (a b : Array Int) →
  (result : Array Int) →
  dissimilarElements-precond a b →
  Set
dissimilarElements-postcond a b result h-precond =
  All
    (λ x → Not (inArray a x ≡ inArray b x))
    result ∧
  Pairwise IntLessOrEqual result ∧
  NoDuplicates result ∧
  All
    (λ x →
      chooseSet
        (inArray b x)
        (Not (x ∈ result))
        (x ∈ result))
    a ∧
  All
    (λ x →
      chooseSet
        (inArray a x)
        (Not (x ∈ result))
        (x ∈ result))
    b

dissimilarElements-spec-satisfied : Set
dissimilarElements-spec-satisfied =
  (a b : Array Int) →
  (h-precond : dissimilarElements-precond a b) →
  dissimilarElements-postcond
    a
    b
    (dissimilarElements a b h-precond)
    h-precond
