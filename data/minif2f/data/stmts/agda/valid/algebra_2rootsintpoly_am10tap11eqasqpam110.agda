-- Statement-only formalization of miniF2F valid artifact
-- algebra_2rootsintpoly_am10tap11eqasqpam110 using rational Cauchy sequences
-- for the standard complex numbers: (a - 10)(a + 11) = a squared + a - 110.
-- This file contains no proof.

module algebra_2rootsintpoly_am10tap11eqasqpam110 where

open import Agda.Builtin.Int using (Int; pos; negsuc)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)

infix 4 _≤ₙ_
infixr 3 _∧_

record _∧_ (A B : Set) : Set where
  constructor both
  field
    first  : A
    second : B

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

ratFromInt : Int → Rational
ratFromInt z = fraction z zero

ratFromNat : Nat → Rational
ratFromNat n = ratFromInt (pos n)

ratZero ratOne : Rational
ratZero = ratFromNat 0
ratOne = ratFromNat 1

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

sequenceAdd : Sequence → Sequence → Sequence
sequenceAdd x y n = ratAdd (x n) (y n)

sequenceNegate : Sequence → Sequence
sequenceNegate x n = ratNegate (x n)

sequenceMultiply : Sequence → Sequence → Sequence
sequenceMultiply x y n = ratMultiply (x n) (y n)

record Complex : Set where
  constructor complex
  field
    realPart      : Real
    imaginaryPart : Real

record ComplexRepresentative : Set where
  constructor representative
  field
    realSequence      : Sequence
    imaginarySequence : Sequence

complexRepresentative : Complex → ComplexRepresentative
complexRepresentative z =
  representative
    (approximation (Complex.realPart z))
    (approximation (Complex.imaginaryPart z))

complexEquivalent :
  ComplexRepresentative →
  ComplexRepresentative →
  Set
complexEquivalent (representative a b) (representative c d) =
  SequenceEquivalent a c ∧ SequenceEquivalent b d

complexAdd :
  ComplexRepresentative →
  ComplexRepresentative →
  ComplexRepresentative
complexAdd (representative a b) (representative c d) =
  representative
    (sequenceAdd a c)
    (sequenceAdd b d)

complexNegate :
  ComplexRepresentative →
  ComplexRepresentative
complexNegate (representative a b) =
  representative
    (sequenceNegate a)
    (sequenceNegate b)

complexSubtract :
  ComplexRepresentative →
  ComplexRepresentative →
  ComplexRepresentative
complexSubtract x y = complexAdd x (complexNegate y)

complexMultiply :
  ComplexRepresentative →
  ComplexRepresentative →
  ComplexRepresentative
complexMultiply (representative a b) (representative c d) =
  representative
    (sequenceSubtract
      (sequenceMultiply a c)
      (sequenceMultiply b d))
    (sequenceAdd
      (sequenceMultiply a d)
      (sequenceMultiply b c))
  where
  sequenceSubtract : Sequence → Sequence → Sequence
  sequenceSubtract x y = sequenceAdd x (sequenceNegate y)

complexFromNat : Nat → ComplexRepresentative
complexFromNat n =
  representative
    (constantSequence (ratFromNat n))
    (constantSequence ratZero)

complexPower :
  ComplexRepresentative →
  Nat →
  ComplexRepresentative
complexPower z zero = complexFromNat 1
complexPower z (suc n) =
  complexMultiply z (complexPower z n)

algebra_2rootsintpoly_am10tap11eqasqpam110 : Set
algebra_2rootsintpoly_am10tap11eqasqpam110 =
  (a : Complex) →
  complexEquivalent
    (complexMultiply
      (complexSubtract
        (complexRepresentative a)
        (complexFromNat 10))
      (complexAdd
        (complexRepresentative a)
        (complexFromNat 11)))
    (complexSubtract
      (complexAdd
        (complexPower (complexRepresentative a) 2)
        (complexRepresentative a))
      (complexFromNat 110))
