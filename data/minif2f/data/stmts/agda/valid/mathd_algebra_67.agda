-- Statement-only formalization of miniF2F valid artifact mathd_algebra_67:
-- for real functions f(x) = 5x + 3 and g(x) = x^2 - 2, g(f(-1)) = 2.
-- The reals use rational Cauchy sequences. This file contains no proof.

{-# OPTIONS --safe #-}

module mathd-algebra-67 where

open import Agda.Builtin.Int using (Int; pos; negsuc)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)

infix 4 _≤ₙ_ _≈ℝ_
infixl 6 _+ℝ_ _-ℝ_
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

-- Cauchy sequences modulo _≈ℝ_ are the standard real numbers.
_≈ℝ_ : Sequence → Sequence → Set
_≈ℝ_ = SequenceEquivalent

constantSequence : Rational → Sequence
constantSequence q n = q

naturalSequence : Nat → Sequence
naturalSequence n = constantSequence (ratFromNat n)

negateSequence : Sequence → Sequence
negateSequence x n = ratNegate (x n)

_+ℝ_ : Sequence → Sequence → Sequence
(x +ℝ y) n = ratAdd (x n) (y n)

_-ℝ_ : Sequence → Sequence → Sequence
x -ℝ y = x +ℝ negateSequence y

_*ℝ_ : Sequence → Sequence → Sequence
(x *ℝ y) n = ratMultiply (x n) (y n)

negativeOne : Sequence
negativeOne = negateSequence (naturalSequence 1)

fFormula : Sequence → Sequence
fFormula x = naturalSequence 5 *ℝ x +ℝ naturalSequence 3

gFormula : Sequence → Sequence
gFormula x = x *ℝ x -ℝ naturalSequence 2

-- A RealFunction is precisely a function on the Cauchy-sequence quotient:
-- it maps real representatives to real representatives and respects equality.
record RealFunction : Set where
  field
    apply : Sequence → Sequence

    maps-cauchy :
      (x : Sequence) →
      Cauchy x →
      Cauchy (apply x)

    respects-equality :
      (x y : Sequence) →
      Cauchy x →
      Cauchy y →
      x ≈ℝ y →
      apply x ≈ℝ apply y

mathd-algebra-67 : Set
mathd-algebra-67 =
  (f g : RealFunction) →
  ((x : Sequence) →
    Cauchy x →
    RealFunction.apply f x ≈ℝ fFormula x) →
  ((x : Sequence) →
    Cauchy x →
    RealFunction.apply g x ≈ℝ gFormula x) →
  RealFunction.apply g (RealFunction.apply f negativeOne)
    ≈ℝ naturalSequence 2
