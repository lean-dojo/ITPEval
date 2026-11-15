-- Statement-only formalization of VERINA corpus artifact verina_basic_108,
-- catalog title "below_zero": a deterministic integer-list program builds all
-- cumulative sums from zero and reports whether one is negative, with its full
-- size, recurrence, and Boolean correctness contract. This file contains no proof.

{-# OPTIONS --safe #-}

module VerinaBasic108 where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Int using (Int; negsuc; pos)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Maybe using (Maybe; just; nothing)
open import Agda.Builtin.Nat using (Nat; zero; suc)

infixr 3 _∧_
infixr 4 _,_
infixr 5 _×_

record Top : Set where
  constructor top

record _∧_ (A B : Set) : Set where
  constructor both
  field
    left-conjunct : A
    right-conjunct : B

record _×_ (A B : Set) : Set where
  constructor _,_
  field
    pairFirst : A
    pairSecond : B

open _×_ public

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

natLess : Nat → Nat → Bool
natLess zero zero = false
natLess zero (suc _) = true
natLess (suc _) zero = false
natLess (suc m) (suc n) = natLess m n

natSubtract : Nat → Nat → Nat
natSubtract m zero = m
natSubtract zero (suc n) = zero
natSubtract (suc m) (suc n) = natSubtract m n

intEqual : Int → Int → Bool
intEqual (pos m) (pos n) = natEqual m n
intEqual (pos _) (negsuc _) = false
intEqual (negsuc _) (pos _) = false
intEqual (negsuc m) (negsuc n) = natEqual m n

intLess : Int → Int → Bool
intLess (pos m) (pos n) = natLess m n
intLess (pos _) (negsuc _) = false
intLess (negsuc _) (pos _) = true
intLess (negsuc m) (negsuc n) = natLess n m

intLessOrEqual : Int → Int → Bool
intLessOrEqual x y =
  if intLess y x
  then false
  else true

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

Array : Set → Set
Array A = List A

arraySize : {A : Set} → Array A → Nat
arraySize [] = zero
arraySize (_ ∷ xs) = suc (arraySize xs)

indexMaybe : {A : Set} → Array A → Nat → Maybe A
indexMaybe [] index = nothing
indexMaybe (x ∷ xs) zero = just x
indexMaybe (x ∷ xs) (suc index) = indexMaybe xs index

indexDefault : {A : Set} → A → Array A → Nat → A
indexDefault default [] index = default
indexDefault default (x ∷ xs) zero = x
indexDefault default (x ∷ xs) (suc index) =
  indexDefault default xs index

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

maybeIntEqual : Maybe Int → Maybe Int → Bool
maybeIntEqual nothing nothing = true
maybeIntEqual nothing (just _) = false
maybeIntEqual (just _) nothing = false
maybeIntEqual (just x) (just y) = intEqual x y

buildSFrom : Int → List Int → Array Int
buildSFrom current [] = current ∷ []
buildSFrom current (operation ∷ operations) =
  current ∷
  buildSFrom (intAdd current operation) operations

buildS : List Int → Array Int
buildS operations = buildSFrom zeroInt operations

checkNegative : List Int → Bool
checkNegative [] = false
checkNegative (x ∷ xs) =
  if intLess x zeroInt
  then true
  else checkNegative xs

below-zero-precond : List Int → Set
below-zero-precond operations = Top

below-zero :
  (operations : List Int) →
  below-zero-precond operations →
  Array Int × Bool
below-zero operations h-precond =
  let s = buildS operations
      result = checkNegative s
  in s , result

below-zero-postcond :
  (operations : List Int) →
  (output : Array Int × Bool) →
  below-zero-precond operations →
  Set
below-zero-postcond operations output h-precond =
  let s = pairFirst output
      result = pairSecond output
  in
    (arraySize s ≡ suc (arraySize operations)) ∧
    (indexMaybe s zero ≡ just zeroInt) ∧
    IsTrue
      (allList
        (λ i →
          maybeIntEqual
            (indexMaybe s (suc i))
            (just
              (intAdd
                (indexDefault zeroInt s i)
                (indexDefault zeroInt operations i))))
        (range (natSubtract (arraySize s) (suc zero)))) ∧
    ((result ≡ true) →
      IsTrue
        (anyList
          (λ i → intLess (indexDefault zeroInt s (suc i)) zeroInt)
          (range (arraySize operations)))) ∧
    ((result ≡ false) →
      IsTrue
        (allList
          (λ x → intLessOrEqual zeroInt x)
          s))

below-zero-spec-satisfied : Set
below-zero-spec-satisfied =
  (operations : List Int) →
  (h-precond : below-zero-precond operations) →
  below-zero-postcond
    operations
    (below-zero operations h-precond)
    h-precond
