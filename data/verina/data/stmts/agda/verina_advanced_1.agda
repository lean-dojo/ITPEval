-- Statement-only formalization of VERINA corpus artifact verina_advanced_1,
-- catalog title "FindSingleNumber": a deterministic list program returns the
-- sole integer occurring once when every other listed integer occurs twice.
-- This file contains no proof.

{-# OPTIONS --safe #-}

module VerinaAdvanced1 where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Int using (Int; negsuc; pos)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc)

infixr 3 _∨_
infixr 4 _∧_
infix 4 _≤_ _<_ _∈_
infixr 5 _||_

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

intEqual : Int → Int → Bool
intEqual (pos m) (pos n) = natEqual m n
intEqual (pos _) (negsuc _) = false
intEqual (negsuc _) (pos _) = false
intEqual (negsuc m) (negsuc n) = natEqual m n

one : Nat
one = suc zero

two : Nat
two = suc one

listLength : {A : Set} → List A → Nat
listLength [] = zero
listLength (_ ∷ xs) = suc (listLength xs)

mapList : {A B : Set} → (A → B) → List A → List B
mapList f [] = []
mapList f (x ∷ xs) = f x ∷ mapList f xs

filterlist : Int → List Int → List Int
filterlist x [] = []
filterlist x (y ∷ ys) =
  if intEqual y x
  then y ∷ filterlist x ys
  else filterlist x ys

countInt : Int → List Int → Nat
countInt x nums = listLength (filterlist x nums)

countNat : Nat → List Nat → Nat
countNat sought [] = zero
countNat sought (x ∷ xs) =
  if natEqual x sought
  then suc (countNat sought xs)
  else countNat sought xs

numsCount : List Int → List Nat
numsCount nums = mapList (λ x → countInt x nums) nums

allowedCount : Nat → Bool
allowedCount count = natEqual count one || natEqual count two

allAllowed : List Nat → Bool
allAllowed [] = true
allAllowed (count ∷ counts) =
  if allowedCount count
  then allAllowed counts
  else false

data IsTrue : Bool → Set where
  true-witness : IsTrue true

record FindSingleNumber-precond (nums : List Int) : Set where
  constructor precondition
  field
    every-count-is-one-or-two : IsTrue (allAllowed (numsCount nums))
    exactly-one-count-is-one : countNat one (numsCount nums) ≡ one

findUnique : List Int → List Int → Int
findUnique original [] = pos zero
findUnique original (x ∷ xs) =
  if natEqual (listLength (filterlist x original)) one
  then x
  else findUnique original xs

FindSingleNumber :
  (nums : List Int) →
  FindSingleNumber-precond nums →
  Int
FindSingleNumber nums h-precond = findUnique nums nums

data _≤_ : Nat → Nat → Set where
  zero≤ : {n : Nat} → zero ≤ n
  suc≤suc : {m n : Nat} → m ≤ n → suc m ≤ suc n

_<_ : Nat → Nat → Set
m < n = suc m ≤ n

record _∧_ (A B : Set) : Set where
  constructor both
  field
    first : A
    second : B

data _∨_ (A B : Set) : Set where
  left : A → A ∨ B
  right : B → A ∨ B

data _∈_ (x : Int) : List Int → Set where
  here : {xs : List Int} → x ∈ (x ∷ xs)
  there : {y : Int} {xs : List Int} → x ∈ xs → x ∈ (y ∷ xs)

FindSingleNumber-postcond :
  (nums : List Int) →
  (result : Int) →
  FindSingleNumber-precond nums →
  Set
FindSingleNumber-postcond nums result h-precond =
  (zero < listLength nums) ∧
  ((listLength (filterlist result nums) ≡ one) ∧
  ((x : Int) →
    x ∈ nums →
    (x ≡ result) ∨
    (listLength (filterlist x nums) ≡ two)))

FindSingleNumber-spec-satisfied : Set
FindSingleNumber-spec-satisfied =
  (nums : List Int) →
  (h-precond : FindSingleNumber-precond nums) →
  FindSingleNumber-postcond
    nums
    (FindSingleNumber nums h-precond)
    h-precond
