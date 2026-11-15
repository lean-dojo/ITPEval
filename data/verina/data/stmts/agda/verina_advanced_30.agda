-- Statement-only formalization of VERINA corpus artifact verina_advanced_30,
-- catalog title "longestIncreasingStreak": a deterministic integer-list
-- program computes the length of the longest strictly increasing contiguous
-- streak and is connected to its full correctness contract. This file contains no proof.

{-# OPTIONS --safe #-}

module VerinaAdvanced30 where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Int using (Int; negsuc; pos)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Maybe using (Maybe; just; nothing)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)

infixr 2 _∨_
infixr 3 _∧_
infixr 5 _&&_
infixr 4 _||_
infix 4 _<_

record Top : Set where
  constructor top

record _∧_ (A B : Set) : Set where
  constructor both
  field
    first : A
    second : B

data _∨_ (A B : Set) : Set where
  or-left : A → A ∨ B
  or-right : B → A ∨ B

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

_&&_ : Bool → Bool → Bool
true && other = other
false && other = false

_||_ : Bool → Bool → Bool
true || other = true
false || other = other

notBool : Bool → Bool
notBool true = false
notBool false = true

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

natGreaterOrEqual : Nat → Nat → Bool
natGreaterOrEqual m n = natLessOrEqual n m

natSubtract : Nat → Nat → Nat
natSubtract m zero = m
natSubtract zero (suc n) = zero
natSubtract (suc m) (suc n) = natSubtract m n

natMax : Nat → Nat → Nat
natMax m n =
  if natLess m n
  then n
  else m

intLess : Int → Int → Bool
intLess (pos m) (pos n) = natLess m n
intLess (pos _) (negsuc _) = false
intLess (negsuc _) (pos _) = true
intLess (negsuc m) (negsuc n) = natLess n m

intGreaterOrEqual : Int → Int → Bool
intGreaterOrEqual m n = notBool (intLess m n)

one : Nat
one = suc zero

zeroInt : Int
zeroInt = pos zero

listLength : {A : Set} → List A → Nat
listLength [] = zero
listLength (_ ∷ xs) = suc (listLength xs)

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

anyList : {A : Set} → (A → Bool) → List A → Bool
anyList predicate [] = false
anyList predicate (x ∷ xs) =
  if predicate x
  then true
  else anyList predicate xs

nthDefault : {A : Set} → A → Nat → List A → A
nthDefault default zero [] = default
nthDefault default zero (x ∷ xs) = x
nthDefault default (suc n) [] = default
nthDefault default (suc n) (_ ∷ xs) =
  nthDefault default n xs

longestIncreasingStreak-precond : List Int → Set
longestIncreasingStreak-precond nums = Top

longestIncreasingStreak-aux :
  List Int → Maybe Int → Nat → Nat → Nat
longestIncreasingStreak-aux [] previous current maximum =
  natMax current maximum
longestIncreasingStreak-aux
  (x ∷ xs)
  nothing
  current
  maximum =
    longestIncreasingStreak-aux
      xs
      (just x)
      one
      (natMax one maximum)
longestIncreasingStreak-aux
  (x ∷ xs)
  (just previous)
  current
  maximum =
    if intLess previous x
    then
      longestIncreasingStreak-aux
        xs
        (just x)
        (current + one)
        (natMax (current + one) maximum)
    else
      longestIncreasingStreak-aux
        xs
        (just x)
        one
        (natMax current maximum)

longestIncreasingStreak :
  (nums : List Int) →
  longestIncreasingStreak-precond nums →
  Nat
longestIncreasingStreak nums h-precond =
  longestIncreasingStreak-aux nums nothing zero zero

strictlyIncreasingPairs :
  List Int → Nat → Nat → Bool
strictlyIncreasingPairs nums start result =
  allList
    (λ i →
      intLess
        (nthDefault zeroInt (start + i) nums)
        (nthDefault zeroInt (start + i + one) nums))
    (range (natSubtract result one))

maximalOnLeft :
  List Int → Nat → Bool
maximalOnLeft nums start =
  natEqual start zero ||
  intGreaterOrEqual
    (nthDefault zeroInt (natSubtract start one) nums)
    (nthDefault zeroInt start nums)

maximalOnRight :
  List Int → Nat → Nat → Bool
maximalOnRight nums start result =
  natEqual (start + result) (listLength nums) ||
  intGreaterOrEqual
    (nthDefault
      zeroInt
      (natSubtract (start + result) one)
      nums)
    (nthDefault zeroInt (start + result) nums)

isExactMaximalStreak :
  List Int → Nat → Nat → Bool
isExactMaximalStreak nums result start =
  natLessOrEqual (start + result) (listLength nums) &&
  strictlyIncreasingPairs nums start result &&
  maximalOnLeft nums start &&
  maximalOnRight nums start result

hasExactMaximalStreak :
  List Int → Nat → Bool
hasExactMaximalStreak nums result =
  anyList
    (isExactMaximalStreak nums result)
    (range (natSubtract (listLength nums) result + one))

hasFailureInLongerWindow :
  List Int → Nat → Nat → Bool
hasFailureInLongerWindow nums result start =
  anyList
    (λ i →
      natGreaterOrEqual
        (start + i + one)
        (listLength nums) ||
      intGreaterOrEqual
        (nthDefault zeroInt (start + i) nums)
        (nthDefault zeroInt (start + i + one) nums))
    (range result)

noLongerStreak :
  List Int → Nat → Bool
noLongerStreak nums result =
  allList
    (hasFailureInLongerWindow nums result)
    (range (natSubtract (listLength nums) result))

longestIncreasingStreak-postcond :
  (nums : List Int) →
  (result : Nat) →
  longestIncreasingStreak-precond nums →
  Set
longestIncreasingStreak-postcond nums result h-precond =
  (nums ≡ [] → result ≡ zero) ∧
  (zero < result →
    IsTrue (hasExactMaximalStreak nums result)) ∧
  IsTrue (noLongerStreak nums result)

longestIncreasingStreak-spec-satisfied : Set
longestIncreasingStreak-spec-satisfied =
  (nums : List Int) →
  (h-precond : longestIncreasingStreak-precond nums) →
  longestIncreasingStreak-postcond
    nums
    (longestIncreasingStreak nums h-precond)
    h-precond
