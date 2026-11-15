-- Statement-only formalization of miniF2F valid problem mathd_algebra_192:
-- multiplying the conjugate complex numbers 11 - 5i and 11 + 5i by 2i gives 292i.
-- Standard complex numbers use rational Cauchy-sequence real coordinates. This file
-- contains no proof.

{-# OPTIONS --safe #-}

module mathd-algebra-192 where

open import Agda.Builtin.Int using (Int; pos; negsuc)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)

infix 4 _≤ₙ_
infixr 3 _∧_

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

record Real : Set where
  constructor cauchyReal
  field
    approximation : Sequence
    cauchy         : Cauchy approximation

open Real public

-- This is equality in the Cauchy completion, not equality of representatives.
SequenceEquivalent : Sequence → Sequence → Set
SequenceEquivalent first second =
  (precision : Nat) →
  Exists Nat
    (λ cutoff →
      (n : Nat) →
      cutoff ≤ₙ n →
      RationalDistanceWithin
        (first n)
        (second n)
        (unitFraction precision))

constantSequence : Rational → Sequence
constantSequence q n = q

naturalSequence : Nat → Sequence
naturalSequence n = constantSequence (ratFromNat n)

sequenceNegate : Sequence → Sequence
sequenceNegate x n = ratNegate (x n)

sequenceAdd : Sequence → Sequence → Sequence
sequenceAdd x y n = ratAdd (x n) (y n)

sequenceSubtract : Sequence → Sequence → Sequence
sequenceSubtract x y n = ratSubtract (x n) (y n)

sequenceMultiply : Sequence → Sequence → Sequence
sequenceMultiply x y n = ratMultiply (x n) (y n)

record Complex : Set where
  constructor cauchyComplex
  field
    realPart      : Real
    imaginaryPart : Real

open Complex public

record ComplexApproximation : Set where
  constructor complexApproximation
  field
    realSequence      : Sequence
    imaginarySequence : Sequence

open ComplexApproximation public

coordinates : Complex → ComplexApproximation
coordinates z =
  complexApproximation
    (approximation (realPart z))
    (approximation (imaginaryPart z))

complexAdd :
  ComplexApproximation →
  ComplexApproximation →
  ComplexApproximation
complexAdd (complexApproximation a b) (complexApproximation c d) =
  complexApproximation
    (sequenceAdd a c)
    (sequenceAdd b d)

complexNegate : ComplexApproximation → ComplexApproximation
complexNegate (complexApproximation a b) =
  complexApproximation
    (sequenceNegate a)
    (sequenceNegate b)

complexSubtract :
  ComplexApproximation →
  ComplexApproximation →
  ComplexApproximation
complexSubtract x y = complexAdd x (complexNegate y)

complexMultiply :
  ComplexApproximation →
  ComplexApproximation →
  ComplexApproximation
complexMultiply (complexApproximation a b) (complexApproximation c d) =
  complexApproximation
    (sequenceSubtract
      (sequenceMultiply a c)
      (sequenceMultiply b d))
    (sequenceAdd
      (sequenceMultiply a d)
      (sequenceMultiply b c))

complexFromNat : Nat → ComplexApproximation
complexFromNat n =
  complexApproximation
    (naturalSequence n)
    (naturalSequence 0)

complexI : ComplexApproximation
complexI =
  complexApproximation
    (naturalSequence 0)
    (naturalSequence 1)

ComplexEquivalent :
  ComplexApproximation →
  ComplexApproximation →
  Set
ComplexEquivalent x y =
  SequenceEquivalent
    (realSequence x)
    (realSequence y)
  ∧
  SequenceEquivalent
    (imaginarySequence x)
    (imaginarySequence y)

mathd-algebra-192 : Set
mathd-algebra-192 =
  (q e d : Complex) →
  ComplexEquivalent
    (coordinates q)
    (complexSubtract
      (complexFromNat 11)
      (complexMultiply
        (complexFromNat 5)
        complexI)) →
  ComplexEquivalent
    (coordinates e)
    (complexAdd
      (complexFromNat 11)
      (complexMultiply
        (complexFromNat 5)
        complexI)) →
  ComplexEquivalent
    (coordinates d)
    (complexMultiply
      (complexFromNat 2)
      complexI) →
  ComplexEquivalent
    (complexMultiply
      (complexMultiply
        (coordinates q)
        (coordinates e))
      (coordinates d))
    (complexMultiply
      (complexFromNat 292)
      complexI)
