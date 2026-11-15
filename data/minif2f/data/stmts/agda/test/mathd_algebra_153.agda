-- Statement-only formalization of miniF2F test problem mathd_algebra_153:
-- for the real number n = 1/3, four scaled floor values sum to 3702. Reals
-- are represented by rational Cauchy sequences modulo equality of limits,
-- and each floor is characterized by its integer bounds. This file contains
-- no proof.

{-# OPTIONS --safe #-}

module mathd-algebra-153 where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Int using (Int; pos; negsuc)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)

infix 4 _≤ₙ_ _≈ℝ_
infixl 6 _+z_
infixr 4 _∧_

data ⊥ : Set where

record _∧_ (A B : Set) : Set where
  constructor _,_
  field
    left  : A
    right : B

record Exists (A : Set) (P : A → Set) : Set where
  constructor witness
  field
    value    : A
    property : P value

data _≤ₙ_ : Nat → Nat → Set where
  zero≤   : {n : Nat} → zero ≤ₙ n
  suc≤suc : {m n : Nat} → m ≤ₙ n → suc m ≤ₙ suc n

pred : Nat → Nat
pred zero = zero
pred (suc n) = n

negative : Nat → Int
negative zero = pos zero
negative (suc n) = negsuc n

negateInt : Int → Int
negateInt (pos n) = negative n
negateInt (negsuc n) = pos (suc n)

difference : Nat → Nat → Int
difference zero zero = pos zero
difference (suc m) zero = pos (suc m)
difference zero (suc n) = negsuc n
difference (suc m) (suc n) = difference m n

_+z_ : Int → Int → Int
pos m +z pos n = pos (m + n)
pos m +z negsuc n = difference m (suc n)
negsuc m +z pos n = difference n (suc m)
negsuc m +z negsuc n = negsuc (suc (m + n))

multiplyInt : Int → Int → Int
multiplyInt (pos m) (pos n) = pos (m * n)
multiplyInt (pos m) (negsuc n) = negative (m * suc n)
multiplyInt (negsuc m) (pos n) = negative (suc m * n)
multiplyInt (negsuc m) (negsuc n) = pos (suc m * suc n)

scaleInt : Int → Nat → Int
scaleInt z n = multiplyInt z (pos n)

absoluteInt : Int → Nat
absoluteInt (pos n) = n
absoluteInt (negsuc n) = suc n

-- A rational is an integer numerator over one plus denominator-minus-one.
record Rational : Set where
  constructor fraction
  field
    numerator             : Int
    denominator-minus-one : Nat

open Rational public

denominator : Rational → Nat
denominator q = suc (denominator-minus-one q)

ratFromNat : Nat → Rational
ratFromNat n = fraction (pos n) zero

ratFromInt : Int → Rational
ratFromInt z = fraction z zero

ratNegate : Rational → Rational
ratNegate q =
  fraction
    (negateInt (numerator q))
    (denominator-minus-one q)

ratAdd : Rational → Rational → Rational
ratAdd x y =
  fraction
    (scaleInt (numerator x) (denominator y)
      +z scaleInt (numerator y) (denominator x))
    (pred (denominator x * denominator y))

ratSubtract : Rational → Rational → Rational
ratSubtract x y = ratAdd x (ratNegate y)

ratMultiply : Rational → Rational → Rational
ratMultiply x y =
  fraction
    (multiplyInt (numerator x) (numerator y))
    (pred (denominator x * denominator y))

ratAbsolute : Rational → Rational
ratAbsolute q =
  fraction
    (pos (absoluteInt (numerator q)))
    (denominator-minus-one q)

RationalLessOrEqual : Rational → Rational → Set
RationalLessOrEqual x y =
  IntLessOrEqual
    (scaleInt (numerator x) (denominator y))
    (scaleInt (numerator y) (denominator x))
  where
  data IntLessOrEqual : Int → Int → Set where
    positive≤positive :
      {m n : Nat} →
      m ≤ₙ n →
      IntLessOrEqual (pos m) (pos n)
    negative≤positive :
      {m n : Nat} →
      IntLessOrEqual (negsuc m) (pos n)
    negative≤negative :
      {m n : Nat} →
      n ≤ₙ m →
      IntLessOrEqual (negsuc m) (negsuc n)

RationalDistanceWithin : Rational → Rational → Rational → Set
RationalDistanceWithin x y epsilon =
  RationalLessOrEqual
    (ratAbsolute (ratSubtract x y))
    epsilon

unitFraction : Nat → Rational
unitFraction n = fraction (pos 1) n

oneThird : Rational
oneThird = fraction (pos 1) 2

Sequence : Set
Sequence = Nat → Rational

Cauchy : Sequence → Set
Cauchy sequence =
  (precision : Nat) →
  Exists Nat
    (λ cutoff →
      (m n : Nat) →
      cutoff ≤ₙ m →
      cutoff ≤ₙ n →
      RationalDistanceWithin
        (sequence m)
        (sequence n)
        (unitFraction precision))

record Real : Set where
  constructor cauchyReal
  field
    approximation : Sequence
    cauchy         : Cauchy approximation

open Real public

SequenceEquivalent : Sequence → Sequence → Set
SequenceEquivalent left right =
  (precision : Nat) →
  Exists Nat
    (λ cutoff →
      (n : Nat) →
      cutoff ≤ₙ n →
      RationalDistanceWithin
        (left n)
        (right n)
        (unitFraction precision))

-- Cauchy sequences modulo SequenceEquivalent are the real completion of the
-- rationals, so _≈ℝ_ is equality of the represented real numbers.
_≈ℝ_ : Sequence → Sequence → Set
_≈ℝ_ = SequenceEquivalent

RealLessOrEqual : Sequence → Sequence → Set
RealLessOrEqual left right =
  (precision : Nat) →
  Exists Nat
    (λ cutoff →
      (n : Nat) →
      cutoff ≤ₙ n →
      RationalLessOrEqual
        (left n)
        (ratAdd (right n) (unitFraction precision)))

RealStrictlyLess : Sequence → Sequence → Set
RealStrictlyLess left right =
  RealLessOrEqual left right ∧ ((left ≈ℝ right) → ⊥)

constantSequence : Rational → Sequence
constantSequence q n = q

integerSequence : Int → Sequence
integerSequence z = constantSequence (ratFromInt z)

scaleSequence : Nat → Sequence → Sequence
scaleSequence scale sequence n =
  ratMultiply (ratFromNat scale) (sequence n)

FloorOf : Sequence → Int → Set
FloorOf sequence z =
  RealLessOrEqual (integerSequence z) sequence ∧
  RealStrictlyLess sequence (integerSequence (z +z pos 1))

record FourFloors (sequence : Sequence) : Set where
  constructor fourFloors
  field
    floor10 floor100 floor1000 floor10000 : Int
    floor10-correct :
      FloorOf (scaleSequence 10 sequence) floor10
    floor100-correct :
      FloorOf (scaleSequence 100 sequence) floor100
    floor1000-correct :
      FloorOf (scaleSequence 1000 sequence) floor1000
    floor10000-correct :
      FloorOf (scaleSequence 10000 sequence) floor10000
    sum-correct :
      ((floor10 +z floor100) +z floor1000) +z floor10000
      ≡ pos 3702

-- Each FloorOf witness is the unique integer z satisfying z ≤ x < z + 1.
-- Thus FourFloors is bidirectionally equivalent to the source equality of
-- the four standard floor values.
mathd-algebra-153 : Set
mathd-algebra-153 =
  (n : Real) →
  approximation n ≈ℝ constantSequence oneThird →
  FourFloors (approximation n)
