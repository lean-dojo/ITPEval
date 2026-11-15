-- Statement-only formalization of VERINA corpus artifact verina_advanced_56,
-- catalog title "moveZeroes": a deterministic list program stably moves all
-- integer zeroes to the end, preserving the zero count and list length.
-- This file contains no proof.

{-# OPTIONS --safe #-}

module VerinaAdvanced56 where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Int using (Int; negsuc; pos)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc)

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

natEqual : Nat → Nat → Bool
natEqual zero zero = true
natEqual zero (suc _) = false
natEqual (suc _) zero = false
natEqual (suc m) (suc n) = natEqual m n

intEqual : Int → Int → Bool
intEqual (pos m) (pos n) = natEqual m n
intEqual (pos _) (negsuc _) = false
intEqual (negsuc _) (pos _) = false
intEqual (negsuc m) (negsuc n) = natEqual m n

intZero : Int
intZero = pos zero

appendList : {A : Set} → List A → List A → List A
appendList [] ys = ys
appendList (x ∷ xs) ys = x ∷ appendList xs ys

filterList : {A : Set} → (A → Bool) → List A → List A
filterList predicate [] = []
filterList predicate (x ∷ xs) =
  if predicate x
  then x ∷ filterList predicate xs
  else filterList predicate xs

dropWhileList : {A : Set} → (A → Bool) → List A → List A
dropWhileList predicate [] = []
dropWhileList predicate (x ∷ xs) =
  if predicate x
  then dropWhileList predicate xs
  else (x ∷ xs)

allList : {A : Set} → (A → Bool) → List A → Bool
allList predicate [] = true
allList predicate (x ∷ xs) =
  if predicate x
  then allList predicate xs
  else false

listLength : {A : Set} → List A → Nat
listLength [] = zero
listLength (_ ∷ xs) = suc (listLength xs)

moveZeroes-precond : List Int → Set
moveZeroes-precond xs = Top

moveZeroes :
  (xs : List Int) →
  moveZeroes-precond xs →
  List Int
moveZeroes xs h-precond =
  let nonzeros =
        filterList
          (λ x → boolNot (intEqual x intZero))
          xs
      zeros =
        filterList
          (λ x → intEqual x intZero)
          xs
  in appendList nonzeros zeros

countVal : Int → List Int → Nat
countVal val [] = zero
countVal val (x ∷ xs) =
  let rest = countVal val xs
  in
    if intEqual x val
    then suc rest
    else rest

isSubsequence : List Int → List Int → Bool
isSubsequence [] ys = true
isSubsequence (_ ∷ _) [] = false
isSubsequence (x ∷ xt) (y ∷ yt) =
  if intEqual x y
  then isSubsequence xt yt
  else isSubsequence (x ∷ xt) yt

moveZeroes-postcond :
  (xs : List Int) →
  (result : List Int) →
  moveZeroes-precond xs →
  Set
moveZeroes-postcond xs result h-precond =
  (isSubsequence
    (filterList (λ x → boolNot (intEqual x intZero)) xs)
    result ≡ true) ∧
  (allList
    (λ x → intEqual x intZero)
    (dropWhileList
      (λ x → boolNot (intEqual x intZero))
      result) ≡ true) ∧
  (countVal intZero xs ≡ countVal intZero result) ∧
  (listLength xs ≡ listLength result)

moveZeroes-spec-satisfied : Set
moveZeroes-spec-satisfied =
  (xs : List Int) →
  (h-precond : moveZeroes-precond xs) →
  moveZeroes-postcond
    xs
    (moveZeroes xs h-precond)
    h-precond
