-- Statement-only formalization of VERINA corpus artifact verina_basic_79,
-- catalog title "onlineMax": a deterministic integer-array program computes
-- the maximum of the first x entries and the first later entry exceeding it,
-- or the final index if none does, and is connected to its full correctness
-- contract. This file contains no proof.

{-# OPTIONS --safe #-}

module VerinaBasic79 where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Int using (Int; negsuc; pos)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc)

infixr 2 _∨_
infixr 3 _∧_
infixr 4 _,_
infixr 5 _×_
infix 4 _≤_ _<_

data _∨_ (A B : Set) : Set where
  left : A → A ∨ B
  right : B → A ∨ B

record _∧_ (A B : Set) : Set where
  constructor both
  field
    first-conjunct : A
    second-conjunct : B

record _×_ (A B : Set) : Set where
  constructor _,_
  field
    pairFirst : A
    pairSecond : B

open _×_ public

data Exists {A : Set} (P : A → Set) : Set where
  witness : (x : A) → P x → Exists P

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

natLess : Nat → Nat → Bool
natLess zero zero = false
natLess zero (suc _) = true
natLess (suc _) zero = false
natLess (suc m) (suc n) = natLess m n

natLessOrEqual : Nat → Nat → Bool
natLessOrEqual zero _ = true
natLessOrEqual (suc _) zero = false
natLessOrEqual (suc m) (suc n) = natLessOrEqual m n

natSubtract : Nat → Nat → Nat
natSubtract m zero = m
natSubtract zero (suc n) = zero
natSubtract (suc m) (suc n) = natSubtract m n

intLess : Int → Int → Bool
intLess (pos m) (pos n) = natLess m n
intLess (pos _) (negsuc _) = false
intLess (negsuc _) (pos _) = true
intLess (negsuc m) (negsuc n) = natLess n m

intLessOrEqual : Int → Int → Bool
intLessOrEqual (pos m) (pos n) = natLessOrEqual m n
intLessOrEqual (pos _) (negsuc _) = false
intLessOrEqual (negsuc _) (pos _) = true
intLessOrEqual (negsuc m) (negsuc n) =
  natLessOrEqual n m

intGreater : Int → Int → Bool
intGreater x y = intLess y x

IntLessOrEqual : Int → Int → Set
IntLessOrEqual x y = IsTrue (intLessOrEqual x y)

IntGreater : Int → Int → Set
IntGreater x y = IsTrue (intGreater x y)

zeroInt : Int
zeroInt = pos zero

one : Nat
one = suc zero

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

onlineMax-precond : Array Int → Nat → Set
onlineMax-precond a x =
  (zero < arraySize a) ∧
  (zero < x) ∧
  (x < arraySize a)

chooseBest : Int → Int → Int
chooseBest best candidate =
  if intGreater candidate best
  then candidate
  else best

-- Fuel x is sufficient for exactly the source scan from i until i is no
-- longer below x, including arbitrary starting indices.
findBestFuel :
  Array Int → Nat → Nat → Int → Nat → Int
findBestFuel a x i best zero = best
findBestFuel a x i best (suc fuel) =
  if natLess i x
  then findBestFuel
         a
         x
         (suc i)
         (chooseBest best (indexDefault zeroInt a i))
         fuel
  else best

findBest : Array Int → Nat → Nat → Int → Int
findBest a x i best =
  findBestFuel a x i best x

-- Fuel equal to the array size is sufficient for exactly the source scan
-- from i until i reaches or exceeds the array size.
findPFuel :
  Array Int → Nat → Int → Nat → Nat → Nat
findPFuel a x m i zero =
  natSubtract (arraySize a) one
findPFuel a x m i (suc fuel) =
  if natLess i (arraySize a)
  then
    if intGreater (indexDefault zeroInt a i) m
    then i
    else findPFuel a x m (suc i) fuel
  else natSubtract (arraySize a) one

findP : Array Int → Nat → Int → Nat → Nat
findP a x m i =
  findPFuel a x m i (arraySize a)

onlineMax :
  (a : Array Int) →
  (x : Nat) →
  onlineMax-precond a x →
  Int × Nat
onlineMax a x h-precond =
  let best = indexDefault zeroInt a zero
      m = findBest a x one best
      p = findP a x m x
  in m , p

onlineMax-postcond :
  (a : Array Int) →
  (x : Nat) →
  (result : Int × Nat) →
  onlineMax-precond a x →
  Set
onlineMax-postcond a x result h-precond =
  let m = pairFirst result
      p = pairSecond result
  in
  ((x ≤ p) ∧ (p < arraySize a)) ∧
  ((i : Nat) →
    i < x →
    IntLessOrEqual (indexDefault zeroInt a i) m) ∧
  Exists
    (λ i →
      (i < x) ∧
      (indexDefault zeroInt a i ≡ m)) ∧
  ((i : Nat) →
    x ≤ i →
    i < p →
    IntLessOrEqual (indexDefault zeroInt a i) m) ∧
  (IntGreater (indexDefault zeroInt a p) m ∨
    ((p ≡ natSubtract (arraySize a) one) ∧
     ((i : Nat) →
       x ≤ i →
       i < arraySize a →
       IntLessOrEqual (indexDefault zeroInt a i) m)))

onlineMax-spec-satisfied : Set
onlineMax-spec-satisfied =
  (a : Array Int) →
  (x : Nat) →
  (h-precond : onlineMax-precond a x) →
  onlineMax-postcond
    a
    x
    (onlineMax a x h-precond)
    h-precond
