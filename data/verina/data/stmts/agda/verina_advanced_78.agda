-- Statement-only formalization of VERINA corpus artifact verina_advanced_78,
-- catalog title "twoSum": a deterministic recursive search returns the unique
-- increasing pair of indices whose integer values sum to the target, under
-- its exact pair-count precondition. This file contains no proof.

{-# OPTIONS --safe #-}

module VerinaAdvanced78 where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Int using (Int; negsuc; pos)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Maybe using (Maybe; just; nothing)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)

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

if_then_else_ : {A : Set} → Bool → A → A → A
if true then when-true else when-false = when-true
if false then when-true else when-false = when-false

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

intSuccessor : Int → Int
intSuccessor (pos n) = pos (suc n)
intSuccessor (negsuc zero) = pos zero
intSuccessor (negsuc (suc n)) = negsuc n

intPredecessor : Int → Int
intPredecessor (pos zero) = negsuc zero
intPredecessor (pos (suc n)) = pos n
intPredecessor (negsuc n) = negsuc (suc n)

intAdd : Int → Int → Int
intAdd x (pos zero) = x
intAdd x (pos (suc n)) =
  intSuccessor (intAdd x (pos n))
intAdd x (negsuc zero) = intPredecessor x
intAdd x (negsuc (suc n)) =
  intPredecessor (intAdd x (negsuc n))

zeroInt : Int
zeroInt = pos zero

one : Nat
one = suc zero

listLength : {A : Set} → List A → Nat
listLength [] = zero
listLength (_ ∷ xs) = suc (listLength xs)

appendList : {A : Set} → List A → List A → List A
appendList [] ys = ys
appendList (x ∷ xs) ys = x ∷ appendList xs ys

mapList : {A B : Set} → (A → B) → List A → List B
mapList f [] = []
mapList f (x ∷ xs) = f x ∷ mapList f xs

flatMapList : {A B : Set} → (A → List B) → List A → List B
flatMapList f [] = []
flatMapList f (x ∷ xs) =
  appendList (f x) (flatMapList f xs)

dropList : {A : Set} → Nat → List A → List A
dropList zero xs = xs
dropList (suc n) [] = []
dropList (suc n) (_ ∷ xs) = dropList n xs

rangeFrom : Nat → Nat → List Nat
rangeFrom start zero = []
rangeFrom start (suc count) =
  start ∷ rangeFrom (suc start) count

range : Nat → List Nat
range count = rangeFrom zero count

indexDefault : {A : Set} → A → List A → Nat → A
indexDefault default [] index = default
indexDefault default (x ∷ xs) zero = x
indexDefault default (x ∷ xs) (suc index) =
  indexDefault default xs index

countInt : Int → List Int → Nat
countInt sought [] = zero
countInt sought (x ∷ xs) =
  if intEqual sought x
  then suc (countInt sought xs)
  else countInt sought xs

pairwiseSums : List Int → List Int
pairwiseSums nums =
  flatMapList
    (λ i →
      mapList
        (λ y →
          intAdd
            (indexDefault zeroInt nums i)
            y)
        (dropList (suc i) nums))
    (range (listLength nums))

twoSum-precond : List Int → Int → Set
twoSum-precond nums target =
  (one < listLength nums) ∧
  (countInt target (pairwiseSums nums) ≡ one)

record NatPair : Set where
  constructor pair
  field
    pairFirst : Nat
    pairSecond : Nat

open NatPair public

findComplementAux :
  List Int →
  Int →
  Nat →
  Int →
  Nat →
  Maybe Nat
findComplementAux [] target i x j = nothing
findComplementAux (y ∷ ys) target i x j =
  if intEqual (intAdd x y) target
  then just ((i + j) + one)
  else findComplementAux ys target i x (suc j)

findComplement :
  List Int →
  Int →
  Nat →
  Int →
  Maybe Nat
findComplement nums target i x =
  findComplementAux nums target i x zero

twoSumAux : List Int → Int → Nat → NatPair
twoSumAux [] target i = pair zero zero
twoSumAux (x ∷ xs) target i
  with findComplement xs target i x
... | just j = pair i j
... | nothing = twoSumAux xs target (suc i)

twoSum :
  (nums : List Int) →
  (target : Int) →
  twoSum-precond nums target →
  NatPair
twoSum nums target h-precond =
  twoSumAux nums target zero

twoSum-postcond :
  (nums : List Int) →
  (target : Int) →
  (result : NatPair) →
  twoSum-precond nums target →
  Set
twoSum-postcond nums target result h-precond =
  let i = pairFirst result
      j = pairSecond result
  in
    (i < j) ∧
    (i < listLength nums) ∧
    (j < listLength nums) ∧
    (intAdd
      (indexDefault zeroInt nums i)
      (indexDefault zeroInt nums j) ≡ target)

twoSum-spec-satisfied : Set
twoSum-spec-satisfied =
  (nums : List Int) →
  (target : Int) →
  (h-precond : twoSum-precond nums target) →
  twoSum-postcond
    nums
    target
    (twoSum nums target h-precond)
    h-precond
