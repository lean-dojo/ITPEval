-- Statement-only formalization of VERINA corpus artifact verina_advanced_74,
-- catalog title "solution": a deterministic program sums, over all contiguous
-- subarrays, the square of each subarray's number of distinct elements and is
-- connected to its full correctness contract. This file contains no proof.

{-# OPTIONS --safe #-}

module VerinaAdvanced74 where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)

infixr 3 _∧_
infix 4 _≤_

record _∧_ (A B : Set) : Set where
  constructor both
  field
    first : A
    second : B

data _≤_ : Nat → Nat → Set where
  zero≤ : {n : Nat} → zero ≤ n
  suc≤suc : {m n : Nat} → m ≤ n → suc m ≤ suc n

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
natLessOrEqual zero n = true
natLessOrEqual (suc m) zero = false
natLessOrEqual (suc m) (suc n) = natLessOrEqual m n

natSubtract : Nat → Nat → Nat
natSubtract m zero = m
natSubtract zero (suc n) = zero
natSubtract (suc m) (suc n) = natSubtract m n

listLength : {A : Set} → List A → Nat
listLength [] = zero
listLength (_ ∷ xs) = suc (listLength xs)

foldLeft : {A B : Set} → (A → B → A) → A → List B → A
foldLeft step accumulator [] = accumulator
foldLeft step accumulator (x ∷ xs) =
  foldLeft step (step accumulator x) xs

allList : {A : Set} → (A → Bool) → List A → Bool
allList predicate [] = true
allList predicate (x ∷ xs) =
  if predicate x
  then allList predicate xs
  else false

takeList : {A : Set} → Nat → List A → List A
takeList zero xs = []
takeList (suc n) [] = []
takeList (suc n) (x ∷ xs) =
  x ∷ takeList n xs

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

containsNat : Nat → List Nat → Bool
containsNat sought [] = false
containsNat sought (x ∷ xs) =
  if natEqual sought x
  then true
  else containsNat sought xs

insertDistinct : List Nat → Nat → List Nat
insertDistinct seen x =
  if containsNat x seen
  then seen
  else (x ∷ seen)

distinctCount : List Nat → Nat
distinctCount xs =
  listLength (foldLeft insertDistinct [] xs)

subarray : List Nat → Nat → Nat → List Nat
subarray nums i j =
  takeList
    (natSubtract j i + 1)
    (dropList i nums)

withinBounds : Nat → Bool
withinBounds x =
  natLessOrEqual 1 x
  ∧-bool natLessOrEqual x 100
  where
  infixr 3 _∧-bool_
  _∧-bool_ : Bool → Bool → Bool
  true ∧-bool value = value
  false ∧-bool value = false

solution-precond : List Nat → Set
solution-precond nums =
  (1 ≤ listLength nums) ∧
  ((listLength nums ≤ 100) ∧
   IsTrue (allList withinBounds nums))

innerSum : List Nat → Nat → Nat → Nat
innerSum nums n i =
  foldLeft
    (λ accumulator d →
      let current-subarray = subarray nums i (i + d)
          count = distinctCount current-subarray
      in accumulator + count * count)
    zero
    (range (natSubtract n i))

solution : List Nat → Nat
solution nums =
  let n = listLength nums
  in
    foldLeft
      (λ accumulator i →
        accumulator + innerSum nums n i)
      zero
      (range n)

getSubarray-local : List Nat → Nat → Nat → List Nat
getSubarray-local nums i j =
  takeList
    (natSubtract j i + 1)
    (dropList i nums)

distinctCount-local : List Nat → Nat
distinctCount-local xs =
  listLength (foldLeft insertDistinct [] xs)

square-local : Nat → Nat
square-local n = n * n

expectedSum : List Nat → Nat
expectedSum nums =
  let n = listLength nums
  in
    foldLeft
      (λ outer-sum i →
        let inner-sum =
              foldLeft
                (λ current-inner-sum d →
                  let j = i + d
                      current-subarray =
                        getSubarray-local nums i j
                      count =
                        distinctCount-local current-subarray
                  in
                    current-inner-sum +
                    square-local count)
                zero
                (range (natSubtract n i))
        in outer-sum + inner-sum)
      zero
      (range n)

solution-postcond : List Nat → Nat → Set
solution-postcond nums result =
  solution-precond nums →
  ((zero ≤ result) ∧
   (result ≡ expectedSum nums))

solution-spec-satisfied : Set
solution-spec-satisfied =
  (nums : List Nat) →
  solution-postcond nums (solution nums)
