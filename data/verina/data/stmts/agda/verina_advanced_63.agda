-- Statement-only formalization of VERINA corpus artifact verina_advanced_63,
-- catalog title "removeDuplicates": a deterministic recursive program counts
-- the distinct entries of a nondecreasing integer list and is connected to
-- the duplicate-erasure length contract. This file contains no proof.

{-# OPTIONS --safe #-}

module VerinaAdvanced63 where

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

natLessOrEqual : Nat → Nat → Bool
natLessOrEqual zero _ = true
natLessOrEqual (suc _) zero = false
natLessOrEqual (suc m) (suc n) = natLessOrEqual m n

natSubtract : Nat → Nat → Nat
natSubtract m zero = m
natSubtract zero (suc n) = zero
natSubtract (suc m) (suc n) = natSubtract m n

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

IntLessOrEqual : Int → Int → Set
IntLessOrEqual x y = IsTrue (intLessOrEqual x y)

All : {A : Set} → (A → Set) → List A → Set
All predicate [] = Top
All predicate (x ∷ xs) = predicate x ∧ All predicate xs

Pairwise :
  {A : Set} → (A → A → Set) → List A → Set
Pairwise relation [] = Top
Pairwise relation (x ∷ xs) =
  All (relation x) xs ∧ Pairwise relation xs

removeDuplicates-precond : List Int → Set
removeDuplicates-precond nums =
  Pairwise IntLessOrEqual nums

countUniques : Int → List Int → Nat → Nat
countUniques prev [] k = k
countUniques prev (head ∷ tail) k =
  if intEqual head prev
  then countUniques prev tail k
  else countUniques head tail (suc k)

removeDuplicates :
  (nums : List Int) →
  removeDuplicates-precond nums →
  Nat
removeDuplicates [] h-precond = zero
removeDuplicates (head ∷ tail) h-precond =
  countUniques head tail (suc zero)

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

listLength : {A : Set} → List A → Nat
listLength [] = zero
listLength (_ ∷ xs) = suc (listLength xs)

removeDuplicates-postcond :
  (nums : List Int) →
  (result : Nat) →
  removeDuplicates-precond nums →
  Set
removeDuplicates-postcond nums result h-precond =
  (natSubtract result (listLength (eraseDups nums)) ≡ zero) ∧
  IsTrue
    (natLessOrEqual
      (listLength (eraseDups nums))
      result)

removeDuplicates-spec-satisfied : Set
removeDuplicates-spec-satisfied =
  (nums : List Int) →
  (h-precond : removeDuplicates-precond nums) →
  removeDuplicates-postcond
    nums
    (removeDuplicates nums h-precond)
    h-precond
