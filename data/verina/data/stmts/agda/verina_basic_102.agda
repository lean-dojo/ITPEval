-- Statement-only formalization of VERINA corpus artifact verina_basic_102,
-- catalog title "twoSum": a deterministic nested array search returns the
-- lexicographically first increasing pair of indices whose integer values
-- sum to the target, under the source pair-existence precondition. This file
-- contains no proof.

{-# OPTIONS --safe #-}

module VerinaBasic102 where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Int using (Int; negsuc; pos)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Maybe using (Maybe; just; nothing)
open import Agda.Builtin.Nat using (Nat; zero; suc)

infixr 3 _∧_
infix 4 _≤_ _<_

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

_<_ : Nat → Nat → Set
m < n = suc m ≤ n

data IsTrue : Bool → Set where
  true-witness : IsTrue true

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

natSubtract : Nat → Nat → Nat
natSubtract m zero = m
natSubtract zero (suc n) = zero
natSubtract (suc m) (suc n) = natSubtract m n

Array : Set → Set
Array A = List A

arraySize : {A : Set} → Array A → Nat
arraySize [] = zero
arraySize (_ ∷ xs) = suc (arraySize xs)

takeList : {A : Set} → Nat → List A → List A
takeList zero xs = []
takeList (suc n) [] = []
takeList (suc n) (x ∷ xs) =
  x ∷ takeList n xs

dropList : {A : Set} → Nat → List A → List A
dropList zero xs = xs
dropList (suc n) [] = []
dropList (suc n) (_ ∷ xs) = dropList n xs

indexDefault : {A : Set} → A → List A → Nat → A
indexDefault default [] index = default
indexDefault default (x ∷ xs) zero = x
indexDefault default (x ∷ xs) (suc index) =
  indexDefault default xs index

All : {A : Set} → (A → Set) → List A → Set
All predicate [] = Top
All predicate (x ∷ xs) =
  predicate x ∧ All predicate xs

Pairwise :
  {A : Set} → (A → A → Set) → List A → Set
Pairwise relation [] = Top
Pairwise relation (x ∷ xs) =
  All (relation x) xs ∧ Pairwise relation xs

allList : {A : Set} → (A → Bool) → List A → Bool
allList predicate [] = true
allList predicate (x ∷ xs) =
  if predicate x
  then allList predicate xs
  else false

record NatPair : Set where
  constructor pair
  field
    pairFirst : Nat
    pairSecond : Nat

open NatPair public

record IndexedInt : Set where
  constructor indexed
  field
    indexedValue : Int
    indexedPosition : Nat

open IndexedInt public

zipIdxFrom : Nat → List Int → List IndexedInt
zipIdxFrom position [] = []
zipIdxFrom position (x ∷ xs) =
  indexed x position ∷ zipIdxFrom (suc position) xs

zipIdx : List Int → List IndexedInt
zipIdx nums = zipIdxFrom zero nums

NoTargetSum : Int → Int → Int → Set
NoTargetSum target x y =
  Not (intAdd x y ≡ target)

twoSum-precond : Array Int → Int → Set
twoSum-precond nums target =
  (one < arraySize nums) ∧
  Not (Pairwise (NoTargetSum target) nums)

findPartner :
  Int →
  List Int →
  Int →
  Nat →
  Maybe Nat
findPartner x [] target j = nothing
findPartner x (y ∷ ys) target j =
  if intEqual (intAdd x y) target
  then just j
  else findPartner x ys target (suc j)

twoSumAux :
  List Int →
  Int →
  Nat →
  NatPair
twoSumAux [] target i = pair zero zero
twoSumAux (x ∷ xs) target i
  with findPartner x xs target (suc i)
... | just j = pair i j
... | nothing = twoSumAux xs target (suc i)

twoSum :
  (nums : Array Int) →
  (target : Int) →
  twoSum-precond nums target →
  NatPair
twoSum nums target h-precond =
  twoSumAux nums target zero

noEarlierFirstPair :
  List Int →
  Int →
  Nat →
  Bool
noEarlierFirstPair nums target i =
  allList
    (λ entry →
      allList
        (λ b →
          boolNot
            (intEqual
              (intAdd (indexedValue entry) b)
              target))
        (dropList (suc (indexedPosition entry)) nums))
    (zipIdx (takeList i nums))

noEarlierPartner :
  List Int →
  Int →
  Nat →
  Nat →
  Bool
noEarlierPartner nums target i j =
  allList
    (λ b →
      boolNot
        (intEqual
          (intAdd (indexDefault zeroInt nums i) b)
          target))
    (takeList
      (natSubtract (natSubtract j i) one)
      (dropList (suc i) nums))

twoSum-postcond :
  (nums : Array Int) →
  (target : Int) →
  (result : NatPair) →
  twoSum-precond nums target →
  Set
twoSum-postcond nums target result h-precond =
  let i = pairFirst result
      j = pairSecond result
  in
    (i < j) ∧
    (j < arraySize nums) ∧
    (intAdd
      (indexDefault zeroInt nums i)
      (indexDefault zeroInt nums j) ≡ target) ∧
    IsTrue (noEarlierFirstPair nums target i) ∧
    IsTrue (noEarlierPartner nums target i j)

twoSum-spec-satisfied : Set
twoSum-spec-satisfied =
  (nums : Array Int) →
  (target : Int) →
  (h-precond : twoSum-precond nums target) →
  twoSum-postcond
    nums
    target
    (twoSum nums target h-precond)
    h-precond
