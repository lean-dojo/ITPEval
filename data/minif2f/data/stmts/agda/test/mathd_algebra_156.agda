-- Statement-only formalization of miniF2F test problem mathd_algebra_156:
-- two intersections of y = x^4 and y = 5x^2 - 6 whose squared inputs are
-- strictly ordered have squared-input difference 1. The reals are rational
-- Cauchy sequences modulo equality of limits. This file contains no proof.

module mathd-algebra-156 where

open import Agda.Builtin.Int using (Int; pos; negsuc)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)

infix 4 _≤ₙ_

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

unitFraction : Nat → Rational
unitFraction n = fraction (pos 1) n

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

-- This is equality in the Cauchy completion of the rationals.
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

-- For convergent rational presentations, an eventual positive rational gap
-- is equivalent to strict order of their real limits.
SequenceStrictLess : Sequence → Sequence → Set
SequenceStrictLess left right =
  Exists Nat
    (λ margin →
      Exists Nat
        (λ cutoff →
          (n : Nat) →
          cutoff ≤ₙ n →
          RationalLessOrEqual
            (ratAdd (left n) (unitFraction margin))
            (right n)))

naturalSequence : Nat → Sequence
naturalSequence n index = ratFromNat n

sequenceSubtract : Sequence → Sequence → Sequence
sequenceSubtract left right index =
  ratSubtract (left index) (right index)

sequenceMultiply : Sequence → Sequence → Sequence
sequenceMultiply left right index =
  ratMultiply (left index) (right index)

sequenceScale : Nat → Sequence → Sequence
sequenceScale coefficient sequence index =
  ratMultiply (ratFromNat coefficient) (sequence index)

sequencePower : Sequence → Nat → Sequence
sequencePower sequence zero = naturalSequence 1
sequencePower sequence (suc exponent) =
  sequenceMultiply sequence (sequencePower sequence exponent)

quadraticSequence : Sequence → Sequence
quadraticSequence sequence =
  sequenceSubtract
    (sequenceScale 5 (sequencePower sequence 2))
    (naturalSequence 6)

-- Extensionality makes these exactly functions on Cauchy reals rather than
-- functions that can distinguish equivalent rational presentations.
record RealFunction : Set where
  field
    valueAt :
      Real → Real
    congruent :
      (x y : Real) →
      SequenceEquivalent (approximation x) (approximation y) →
      SequenceEquivalent
        (approximation (valueAt x))
        (approximation (valueAt y))

mathd-algebra-156 : Set
mathd-algebra-156 =
  (x y : Real) →
  (f g : RealFunction) →
  ((t : Real) →
    SequenceEquivalent
      (approximation (RealFunction.valueAt f t))
      (sequencePower (approximation t) 4)) →
  ((t : Real) →
    SequenceEquivalent
      (approximation (RealFunction.valueAt g t))
      (quadraticSequence (approximation t))) →
  SequenceEquivalent
    (approximation (RealFunction.valueAt f x))
    (approximation (RealFunction.valueAt g x)) →
  SequenceEquivalent
    (approximation (RealFunction.valueAt f y))
    (approximation (RealFunction.valueAt g y)) →
  SequenceStrictLess
    (sequencePower (approximation x) 2)
    (sequencePower (approximation y) 2) →
  SequenceEquivalent
    (sequenceSubtract
      (sequencePower (approximation y) 2)
      (sequencePower (approximation x) 2))
    (naturalSequence 1)
