-- Statement-only formalization of VERINA corpus artifact verina_advanced_70,
-- catalog title "semiOrderedPermutation": a deterministic index-based program
-- computes the minimum adjacent swaps needed to place 1 first and n last in a
-- permutation of the integers from 1 through n. This file contains no proof.

{-# OPTIONS --safe #-}

module VerinaAdvanced70 where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Int using (Int; negsuc; pos)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _-_)

infixr 3 _∧_
infix 4 _<_ _∈_

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

data _<_ : Nat → Nat → Set where
  zero<succ : {n : Nat} → zero < suc n
  succ<succ : {m n : Nat} → m < n → suc m < suc n

data IsTrue : Bool → Set where
  true-witness : IsTrue true

if_then_else_ : {A : Set} → Bool → A → A → A
if true then when-true else when-false = when-true
if false then when-true else when-false = when-false

chooseSet : Bool → Set → Set → Set
chooseSet true when-true when-false = when-true
chooseSet false when-true when-false = when-false

boolNot : Bool → Bool
boolNot true = false
boolNot false = true

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

intLessOrEqual : Int → Int → Bool
intLessOrEqual (pos m) (pos n) = natLessOrEqual m n
intLessOrEqual (pos _) (negsuc _) = false
intLessOrEqual (negsuc _) (pos _) = true
intLessOrEqual (negsuc m) (negsuc n) = natLessOrEqual n m

listLength : {A : Set} → List A → Nat
listLength [] = zero
listLength (_ ∷ xs) = suc (listLength xs)

allList : {A : Set} → (A → Bool) → List A → Bool
allList predicate [] = true
allList predicate (x ∷ xs) =
  if predicate x
  then allList predicate xs
  else false

data _∈_ (x : Int) : List Int → Set where
  here : {xs : List Int} → x ∈ (x ∷ xs)
  there : {y : Int} {xs : List Int} → x ∈ xs → x ∈ (y ∷ xs)

NoDuplicates : List Int → Set
NoDuplicates [] = Top
NoDuplicates (x ∷ xs) =
  Not (x ∈ xs) ∧ NoDuplicates xs

oneNat : Nat
oneNat = suc zero

twoNat : Nat
twoNat = suc oneNat

oneInt : Int
oneInt = pos oneNat

inPermutationRange : Nat → Int → Bool
inPermutationRange n x =
  if intLessOrEqual oneInt x
  then intLessOrEqual x (pos n)
  else false

semiOrderedPermutation-precond : List Int → Set
semiOrderedPermutation-precond nums =
  let n = listLength nums
  in
    (zero < n) ∧
    NoDuplicates nums ∧
    IsTrue (allList (inPermutationRange n) nums)

indexOf : Int → List Int → Nat
indexOf sought [] = zero
indexOf sought (x ∷ xs) =
  if intEqual sought x
  then zero
  else suc (indexOf sought xs)

semiOrderedPermutation :
  (nums : List Int) →
  semiOrderedPermutation-precond nums →
  Int
semiOrderedPermutation nums h-precond =
  let length-list = listLength nums
      largest-num = pos length-list
      first-index = indexOf oneInt nums
      last-index = indexOf largest-num nums
      start-position = zero
      end-position = length-list - oneNat
      should-move-one = boolNot (natEqual first-index start-position)
      should-move-last = boolNot (natEqual last-index end-position)
      distance-one =
        if should-move-one then first-index else zero
      distance-last =
        if should-move-last
        then end-position - last-index
        else zero
      total-moves = distance-one + distance-last
      need-adjustment = natLess last-index first-index
      adjusted-moves =
        if need-adjustment
        then total-moves - oneNat
        else total-moves
  in pos adjusted-moves

intSuccessor : Int → Int
intSuccessor (pos n) = pos (suc n)
intSuccessor (negsuc zero) = pos zero
intSuccessor (negsuc (suc n)) = negsuc n

addNatToInt : Int → Nat → Int
addNatToInt x zero = x
addNatToInt x (suc n) =
  intSuccessor (addNatToInt x n)

semiOrderedPermutation-postcond :
  (nums : List Int) →
  (result : Int) →
  semiOrderedPermutation-precond nums →
  Set
semiOrderedPermutation-postcond nums result h-precond =
  let n = listLength nums
      pos1 = indexOf oneInt nums
      posn = indexOf (pos n) nums
      left-side = pos (pos1 + n)
      crossed-right-side =
        addNatToInt (addNatToInt result twoNat) posn
      ordered-right-side =
        addNatToInt (addNatToInt result oneNat) posn
  in
    chooseSet
      (natLess posn pos1)
      (left-side ≡ crossed-right-side)
      (left-side ≡ ordered-right-side)

semiOrderedPermutation-spec-satisfied : Set
semiOrderedPermutation-spec-satisfied =
  (nums : List Int) →
  (h-precond : semiOrderedPermutation-precond nums) →
  semiOrderedPermutation-postcond
    nums
    (semiOrderedPermutation nums h-precond)
    h-precond
