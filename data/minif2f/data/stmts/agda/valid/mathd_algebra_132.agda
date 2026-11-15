-- Statement-only formalization of miniF2F valid problem mathd_algebra_132 using
-- rational Cauchy sequences for the standard real numbers: commuting the
-- functions f(y) = y + 2 and g(y) = y squared at x forces x = -1/2.
-- This file contains no proof.

{-# OPTIONS --safe #-}

module mathd-algebra-132 where

open import Agda.Builtin.Int using (Int; pos; negsuc)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)

infix 4 _≤ₙ_ _≈ℝ_

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

addInt : Int → Int → Int
addInt (pos m) (pos n) = pos (m + n)
addInt (pos m) (negsuc n) = difference m (suc n)
addInt (negsuc m) (pos n) = difference n (suc m)
addInt (negsuc m) (negsuc n) = negsuc (suc (m + n))

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

ratNegate : Rational → Rational
ratNegate q =
  fraction
    (negateInt (numerator q))
    (denominator-minus-one q)

ratAdd : Rational → Rational → Rational
ratAdd x y =
  fraction
    (addInt
      (scaleInt (numerator x) (denominator y))
      (scaleInt (numerator y) (denominator x)))
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

RationalDistanceWithin : Rational → Rational → Rational → Set
RationalDistanceWithin x y epsilon =
  RationalLessOrEqual
    (ratAbsolute (ratSubtract x y))
    epsilon

unitFraction : Nat → Rational
unitFraction n = fraction (pos 1) n

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

-- Rational Cauchy sequences modulo SequenceEquivalent are the standard real
-- completion, and _≈ℝ_ is equality of the represented real numbers.
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

_≈ℝ_ : Sequence → Sequence → Set
_≈ℝ_ = SequenceEquivalent

constantSequence : Rational → Sequence
constantSequence q n = q

naturalSequence : Nat → Sequence
naturalSequence n = constantSequence (ratFromNat n)

sequenceAdd : Sequence → Sequence → Sequence
sequenceAdd left right n = ratAdd (left n) (right n)

sequenceMultiply : Sequence → Sequence → Sequence
sequenceMultiply left right n = ratMultiply (left n) (right n)

square : Sequence → Sequence
square x = sequenceMultiply x x

negativeHalfSequence : Sequence
negativeHalfSequence =
  constantSequence (fraction (negsuc zero) (suc zero))

-- Pointwise sequence operations descend to addition and multiplication on the
-- Cauchy completion, so each _≈ℝ_ below is the corresponding source equality.
mathd-algebra-132 : Set
mathd-algebra-132 =
  (x : Real) →
  (f g : Real → Real) →
  ((y : Real) →
    approximation (f y)
      ≈ℝ sequenceAdd (approximation y) (naturalSequence 2)) →
  ((y : Real) →
    approximation (g y)
      ≈ℝ square (approximation y)) →
  approximation (f (g x)) ≈ℝ approximation (g (f x)) →
  approximation x ≈ℝ negativeHalfSequence
