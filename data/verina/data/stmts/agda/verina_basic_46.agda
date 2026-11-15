-- Statement-only formalization of VERINA corpus artifact verina_basic_46,
-- catalog title "lastPosition": a deterministic scan of a non-decreasing
-- integer array returns the last matching index, or -1 when there is no match,
-- and is connected to its full correctness contract. This file contains no proof.

{-# OPTIONS --safe #-}

module VerinaBasic46 where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Int using (Int; negsuc; pos)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc)

infixr 2 _∨_
infixr 3 _∧_
infix 4 _≤_ _<_

record Top : Set where
  constructor top

data _∨_ (A B : Set) : Set where
  left : A → A ∨ B
  right : B → A ∨ B

record _∧_ (A B : Set) : Set where
  constructor both
  field
    first : A
    second : B

data IsTrue : Bool → Set where
  true-witness : IsTrue true

data _≤_ : Nat → Nat → Set where
  zero≤ : {n : Nat} → zero ≤ n
  suc≤suc : {m n : Nat} → m ≤ n → suc m ≤ suc n

_<_ : Nat → Nat → Set
m < n = suc m ≤ n

if_then_else_ : {A : Set} → Bool → A → A → A
if true then when-true else when-false = when-true
if false then when-true else when-false = when-false

notBool : Bool → Bool
notBool true = false
notBool false = true

natEqual : Nat → Nat → Bool
natEqual zero zero = true
natEqual zero (suc _) = false
natEqual (suc _) zero = false
natEqual (suc m) (suc n) = natEqual m n

natLessOrEqual : Nat → Nat → Bool
natLessOrEqual zero n = true
natLessOrEqual (suc m) zero = false
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
intLessOrEqual (negsuc m) (negsuc n) =
  natLessOrEqual n m

IntLessOrEqual : Int → Int → Set
IntLessOrEqual x y = IsTrue (intLessOrEqual x y)

zeroInt : Int
zeroInt = pos zero

minusOne : Int
minusOne = negsuc zero

intToNat : Int → Nat
intToNat (pos n) = n
intToNat (negsuc n) = zero

Array : Set → Set
Array A = List A

arraySize : {A : Set} → Array A → Nat
arraySize [] = zero
arraySize (_ ∷ xs) = suc (arraySize xs)

indexDefault : {A : Set} → A → Array A → Nat → A
indexDefault default [] index = default
indexDefault default (x ∷ xs) zero = x
indexDefault default (x ∷ xs) (suc index) =
  indexDefault default xs index

dropList : {A : Set} → Nat → List A → List A
dropList zero xs = xs
dropList (suc n) [] = []
dropList (suc n) (_ ∷ xs) = dropList n xs

allList : {A : Set} → (A → Bool) → List A → Bool
allList predicate [] = true
allList predicate (x ∷ xs) =
  if predicate x
  then allList predicate xs
  else false

All : {A : Set} → (A → Set) → List A → Set
All predicate [] = Top
All predicate (x ∷ xs) =
  predicate x ∧ All predicate xs

Pairwise :
  {A : Set} → (A → A → Set) → List A → Set
Pairwise relation [] = Top
Pairwise relation (x ∷ xs) =
  All (relation x) xs ∧ Pairwise relation xs

lastPosition-precond : Array Int → Int → Set
lastPosition-precond arr elem =
  Pairwise IntLessOrEqual arr

lastPosition-loop :
  Array Int → Int → Nat → Int → Int
lastPosition-loop [] elem index current-position =
  current-position
lastPosition-loop (x ∷ xs) elem index current-position =
  if intEqual x elem
  then lastPosition-loop xs elem (suc index) (pos index)
  else lastPosition-loop xs elem (suc index) current-position

lastPosition :
  (arr : Array Int) →
  (elem : Int) →
  lastPosition-precond arr elem →
  Int
lastPosition arr elem h-precond =
  lastPosition-loop arr elem zero minusOne

lastPosition-postcond :
  (arr : Array Int) →
  (elem : Int) →
  (result : Int) →
  lastPosition-precond arr elem →
  Set
lastPosition-postcond arr elem result h-precond =
  ((result ≡ minusOne) ∨
   IntLessOrEqual zeroInt result) ∧
  (IntLessOrEqual zeroInt result →
    (intToNat result < arraySize arr) ∧
    (indexDefault zeroInt arr (intToNat result) ≡ elem) ∧
    IsTrue
      (allList
        (λ x → notBool (intEqual x elem))
        (dropList (suc (intToNat result)) arr))) ∧
  (result ≡ minusOne →
    IsTrue
      (allList
        (λ x → notBool (intEqual x elem))
        arr))

lastPosition-spec-satisfied : Set
lastPosition-spec-satisfied =
  (arr : Array Int) →
  (elem : Int) →
  (h-precond : lastPosition-precond arr elem) →
  lastPosition-postcond
    arr
    elem
    (lastPosition arr elem h-precond)
    h-precond
