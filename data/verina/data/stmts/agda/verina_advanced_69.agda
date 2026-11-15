-- Statement-only formalization of VERINA corpus artifact verina_advanced_69,
-- catalog title "searchInsert": a deterministic linear search on a strictly
-- increasing integer list returns the target's index or its sorted insertion
-- position and is connected to the corresponding correctness contract. This
-- file contains no proof.

{-# OPTIONS --safe #-}

module VerinaAdvanced69 where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Int using (Int; negsuc; pos)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc)

infixr 3 _∧_
infix 4 _≤N_ _<N_

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

natLess : Nat → Nat → Bool
natLess zero zero = false
natLess zero (suc _) = true
natLess (suc _) zero = false
natLess (suc m) (suc n) = natLess m n

natLessOrEqual : Nat → Nat → Bool
natLessOrEqual zero _ = true
natLessOrEqual (suc _) zero = false
natLessOrEqual (suc m) (suc n) = natLessOrEqual m n

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

IntLess : Int → Int → Set
IntLess x y = IsTrue (intLess x y)

IntLessOrEqual : Int → Int → Set
IntLessOrEqual x y = IsTrue (intLessOrEqual x y)

data _≤N_ : Nat → Nat → Set where
  zero≤ : {n : Nat} → zero ≤N n
  suc≤suc : {m n : Nat} → m ≤N n → suc m ≤N suc n

_<N_ : Nat → Nat → Set
m <N n = suc m ≤N n

listLength : {A : Set} → List A → Nat
listLength [] = zero
listLength (_ ∷ xs) = suc (listLength xs)

nthDefault : {A : Set} → A → Nat → List A → A
nthDefault default zero [] = default
nthDefault default zero (x ∷ xs) = x
nthDefault default (suc n) [] = default
nthDefault default (suc n) (_ ∷ xs) =
  nthDefault default n xs

rangeFrom : Nat → Nat → List Nat
rangeFrom start zero = []
rangeFrom start (suc count) =
  start ∷ rangeFrom (suc start) count

range : Nat → List Nat
range count = rangeFrom zero count

allList : {A : Set} → (A → Bool) → List A → Bool
allList predicate [] = true
allList predicate (x ∷ xs) =
  if predicate x
  then allList predicate xs
  else false

All : {A : Set} → (A → Set) → List A → Set
All predicate [] = Top
All predicate (x ∷ xs) =
  predicate x ∧ All predicate xs

Pairwise :
  {A : Set} → (A → A → Set) → List A → Set
Pairwise relation [] = Top
Pairwise relation (x ∷ xs) =
  All (relation x) xs ∧ Pairwise relation xs

searchInsert-precond : List Int → Int → Set
searchInsert-precond xs target =
  Pairwise IntLess xs

searchInsert-helper :
  List Int → Nat → Int → Nat
searchInsert-helper [] index target = index
searchInsert-helper (current ∷ rest) index target =
  if intLessOrEqual target current
  then index
  else searchInsert-helper rest (suc index) target

searchInsert :
  (xs : List Int) →
  (target : Int) →
  searchInsert-precond xs target →
  Nat
searchInsert [] target h-precond = zero
searchInsert (x ∷ xs) target h-precond =
  searchInsert-helper (x ∷ xs) zero target

searchInsert-postcond :
  (xs : List Int) →
  (target : Int) →
  (result : Nat) →
  searchInsert-precond xs target →
  Set
searchInsert-postcond xs target result h-precond =
  (result ≤N listLength xs) ∧
  IsTrue
    (allList
      (λ index →
        intLess
          (nthDefault (pos zero) index xs)
          target)
      (range result)) ∧
  (result <N listLength xs →
    IntLessOrEqual
      target
      (nthDefault (pos zero) result xs))

searchInsert-spec-satisfied : Set
searchInsert-spec-satisfied =
  (xs : List Int) →
  (target : Int) →
  (h-precond : searchInsert-precond xs target) →
  searchInsert-postcond
    xs
    target
    (searchInsert xs target h-precond)
    h-precond
