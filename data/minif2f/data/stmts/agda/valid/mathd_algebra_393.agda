-- Statement-only formalization of miniF2F valid artifact mathd_algebra_393:
-- for the real polynomial bijection sigma(x) = 4 * x^3 + 1, its inverse maps
-- 33 to 2. The reals use rational Cauchy sequences. This file contains no proof.

{-# OPTIONS --safe #-}

module mathd-algebra-393 where

open import Agda.Builtin.Int using (Int; pos; negsuc)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)

infix 4 _≤ₙ_ _≈ℝ_
infixl 6 _+ℝ_
infixl 7 _*ℝ_

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

-- Cauchy sequences modulo _≈ℝ_ form the standard real numbers.
_≈ℝ_ : Sequence → Sequence → Set
_≈ℝ_ = SequenceEquivalent

constantSequence : Rational → Sequence
constantSequence q n = q

naturalSequence : Nat → Sequence
naturalSequence n = constantSequence (ratFromNat n)

_+ℝ_ : Sequence → Sequence → Sequence
(x +ℝ y) n = ratAdd (x n) (y n)

_*ℝ_ : Sequence → Sequence → Sequence
(x *ℝ y) n = ratMultiply (x n) (y n)

powerSequence : Sequence → Nat → Sequence
powerSequence x zero = naturalSequence 1
powerSequence x (suc n) = x *ℝ powerSequence x n

polynomialSequence : Sequence → Sequence
polynomialSequence x =
  naturalSequence 4 *ℝ powerSequence x 3 +ℝ naturalSequence 1

-- This is a bijection of the real Cauchy setoid: both maps preserve real
-- representatives and equality, and are inverse modulo equality of limits.
record RealBijection : Set where
  field
    forward inverse : Sequence → Sequence

    forward-cauchy :
      (x : Sequence) →
      Cauchy x →
      Cauchy (forward x)
    inverse-cauchy :
      (x : Sequence) →
      Cauchy x →
      Cauchy (inverse x)

    forward-respects :
      (x y : Sequence) →
      Cauchy x →
      Cauchy y →
      x ≈ℝ y →
      forward x ≈ℝ forward y
    inverse-respects :
      (x y : Sequence) →
      Cauchy x →
      Cauchy y →
      x ≈ℝ y →
      inverse x ≈ℝ inverse y

    inverse-forward :
      (x : Sequence) →
      Cauchy x →
      inverse (forward x) ≈ℝ x
    forward-inverse :
      (x : Sequence) →
      Cauchy x →
      forward (inverse x) ≈ℝ x

mathd-algebra-393 : Set
mathd-algebra-393 =
  (σ : RealBijection) →
  ((x : Sequence) →
    Cauchy x →
    RealBijection.forward σ x ≈ℝ polynomialSequence x) →
  RealBijection.inverse σ (naturalSequence 33)
    ≈ℝ naturalSequence 2
