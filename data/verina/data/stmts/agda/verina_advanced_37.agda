-- Statement-only formalization of VERINA corpus artifact verina_advanced_37,
-- catalog title "majorityElement": the insertion-sort midpoint program on
-- integer lists, its majority-element precondition and postcondition, and its
-- final correctness proposition. This file contains no proof.

{-# OPTIONS --safe #-}

module VerinaAdvanced37 where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Int using (Int; negsuc; pos)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc)

infixr 3 _∧_
infix 4 _≤_ _<_

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

boolOr : Bool → Bool → Bool
boolOr true right = true
boolOr false right = right

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

insert : Int → List Int → List Int
insert x [] = x ∷ []
insert x (head ∷ tail) =
  if intLessOrEqual x head
  then (x ∷ head ∷ tail)
  else (head ∷ insert x tail)

insertionSort : List Int → List Int
insertionSort [] = []
insertionSort (head ∷ tail) =
  insert head (insertionSort tail)

dropList : {A : Set} → Nat → List A → List A
dropList zero xs = xs
dropList (suc n) [] = []
dropList (suc n) (_ ∷ xs) = dropList n xs

getAt : List Int → Nat → Int
getAt xs index with dropList index xs
... | [] = zeroInt
... | head ∷ tail = head

majorityElement :
  (nums : List Int) →
  majorityElement-precond nums →
  Int
majorityElement nums h-precond =
  let sorted = insertionSort nums
      len = listLength sorted
      mid = half len
  in
    getAt sorted mid

allList : {A : Set} → (A → Bool) → List A → Bool
allList predicate [] = true
allList predicate (x ∷ xs) =
  if predicate x
  then allList predicate xs
  else false

majorityElement-postcond :
  (nums : List Int) →
  (result : Int) →
  majorityElement-precond nums →
  Set
majorityElement-postcond nums result h-precond =
  (half (listLength nums) < countInt result nums) ∧
  IsTrue
    (allList
      (λ x →
        boolOr
          (intEqual x result)
          (natLessOrEqual
            (countInt x nums)
            (half (listLength nums))))
      nums)

majorityElement-spec-satisfied : Set
majorityElement-spec-satisfied =
  (nums : List Int) →
  (h-precond : majorityElement-precond nums) →
  majorityElement-postcond
    nums
    (majorityElement nums h-precond)
    h-precond
