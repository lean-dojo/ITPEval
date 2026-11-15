-- Statement-only formalization of VERINA corpus artifact verina_basic_25,
-- catalog title "sumAndAverage": a positive bounded natural input is scanned
-- from zero through n to compute its integer sum and IEEE-754 floating-point
-- average, with the executable program connected to its closed-form
-- correctness contract. This file contains no proof.

{-# OPTIONS --safe #-}

module VerinaBasic25 where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Float using
  ( Float
  ; primFloatDiv
  ; primFloatEquality
  ; primNatToFloat
  )
open import Agda.Builtin.Int using (Int; negsuc; pos)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)

infix 2 _<_
infixr 3 _∧_
infixr 4 _,_
infixr 5 _×_

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

data IsTrue : Bool → Set where
  true-witness : IsTrue true

data _<_ : Nat → Nat → Set where
  zero-less-suc : {n : Nat} → zero < suc n
  suc-less-suc : {m n : Nat} → m < n → suc m < suc n

if_then_else_ : {A : Set} → Bool → A → A → A
if true then when-true else when-false = when-true
if false then when-true else when-false = when-false

_and_ : Bool → Bool → Bool
true and right = right
false and right = false

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
intEqual (pos m) (negsuc n) = false
intEqual (negsuc m) (pos n) = false
intEqual (negsuc m) (negsuc n) = natEqual m n

pairEqual : Int × Float → Int × Float → Bool
pairEqual (first , second) (other-first , other-second) =
  intEqual first other-first and
  primFloatEquality second other-second

rangeFrom : Nat → Nat → List Nat
rangeFrom start zero = []
rangeFrom start (suc count) =
  start ∷ rangeFrom (suc start) count

range : Nat → List Nat
range count = rangeFrom zero count

sumList : List Nat → Nat
sumList [] = zero
sumList (x ∷ xs) = x + sumList xs

half : Nat → Nat
half zero = zero
half (suc zero) = zero
half (suc (suc n)) = suc (half n)

triangular : Nat → Nat
triangular n = half (n * suc n)

two-to-the-53 : Nat
two-to-the-53 = 9007199254740992

sumAndAverage-precond : Nat → Set
sumAndAverage-precond n =
  (zero < n) ∧ (n < two-to-the-53)

sumAndAverage :
  (n : Nat) →
  sumAndAverage-precond n →
  Int × Float
sumAndAverage n h-precond =
  if natLessOrEqual n zero
  then pos zero , primNatToFloat zero
  else
    let sum = sumList (range (suc n))
        average = primFloatDiv (primNatToFloat sum) (primNatToFloat n)
    in pos sum , average

sumAndAverage-postcond :
  (n : Nat) →
  (result : Int × Float) →
  sumAndAverage-precond n →
  Set
sumAndAverage-postcond n result h-precond =
  ((n ≡ zero) →
    IsTrue
      (pairEqual
        result
        (pos zero , primNatToFloat zero))) ∧
  ((zero < n) →
    IsTrue
      (intEqual
        (pairFirst result)
        (pos (triangular n))) ∧
    IsTrue
      (primFloatEquality
        (pairSecond result)
        (primFloatDiv
          (primNatToFloat (triangular n))
          (primNatToFloat n))))

sumAndAverage-spec-satisfied : Set
sumAndAverage-spec-satisfied =
  (n : Nat) →
  (h-precond : sumAndAverage-precond n) →
  sumAndAverage-postcond
    n
    (sumAndAverage n h-precond)
    h-precond
