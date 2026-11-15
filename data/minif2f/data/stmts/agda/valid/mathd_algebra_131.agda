-- Statement-only formalization of miniF2F valid artifact mathd_algebra_131:
-- two distinct real roots of 2*x^2 - 7*x + 2 have reciprocal shifts summing
-- to -1. This file contains no proof.

{-# OPTIONS --safe #-}

module mathd-algebra-131 where

open import Agda.Builtin.Int using (Int; pos; negsuc)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)

infix 4 _≤ₙ_

data ⊥ : Set where

Not : Set → Set
Not A = A → ⊥

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

-- The stored denominator is one less than its positive mathematical value.
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

-- This is rational inverse, totalized by sending zero to zero.
ratInverse : Rational → Rational
ratInverse (fraction (pos zero) d) = fraction (pos zero) zero
ratInverse (fraction (pos (suc n)) d) = fraction (pos (suc d)) n
ratInverse (fraction (negsuc n) d) = fraction (negsuc d) n

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

-- Rational Cauchy sequences modulo SequenceEquivalent are the standard real
-- completion. The operations below descend to the usual real operations.
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

constantSequence : Rational → Sequence
constantSequence q n = q

naturalSequence : Nat → Sequence
naturalSequence n = constantSequence (ratFromNat n)

sequenceNegate : Sequence → Sequence
sequenceNegate sequence n = ratNegate (sequence n)

sequenceAdd : Sequence → Sequence → Sequence
sequenceAdd left right n = ratAdd (left n) (right n)

sequenceSubtract : Sequence → Sequence → Sequence
sequenceSubtract left right n = ratSubtract (left n) (right n)

sequenceMultiply : Sequence → Sequence → Sequence
sequenceMultiply left right n = ratMultiply (left n) (right n)

sequenceInverse : Sequence → Sequence
sequenceInverse sequence n = ratInverse (sequence n)

sequenceDivide : Sequence → Sequence → Sequence
sequenceDivide numeratorSequence denominatorSequence =
  sequenceMultiply
    numeratorSequence
    (sequenceInverse denominatorSequence)

square : Sequence → Sequence
square x = sequenceMultiply x x

quadratic : Sequence → Sequence
quadratic x =
  sequenceAdd
    (sequenceSubtract
      (sequenceMultiply
        (naturalSequence 2)
        (square x))
      (sequenceMultiply
        (naturalSequence 7)
        x))
    (naturalSequence 2)

reciprocalShift : Real → Sequence
reciprocalShift x =
  sequenceDivide
    (naturalSequence 1)
    (sequenceSubtract
      (approximation x)
      (naturalSequence 1))

negativeOne : Sequence
negativeOne = sequenceNegate (naturalSequence 1)

-- For either root, the denominator x - 1 is nonzero because the displayed
-- quadratic has value -3 at 1. Pointwise rational inverse therefore descends
-- to the same total real division used by the source statements.
mathd-algebra-131 : Set
mathd-algebra-131 =
  (a b : Real) →
  (f : Real → Real) →
  ((x : Real) →
    SequenceEquivalent
      (approximation (f x))
      (quadratic (approximation x))) →
  SequenceEquivalent
    (approximation (f a))
    (naturalSequence 0) →
  SequenceEquivalent
    (approximation (f b))
    (naturalSequence 0) →
  Not
    (SequenceEquivalent
      (approximation a)
      (approximation b)) →
  SequenceEquivalent
    (sequenceAdd
      (reciprocalShift a)
      (reciprocalShift b))
    negativeOne
