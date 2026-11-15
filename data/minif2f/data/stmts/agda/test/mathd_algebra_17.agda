-- Statement-only formalization of miniF2F test problem mathd_algebra_17: a nested
-- principal-square-root equation over the real numbers forces a = 8. This file contains
-- no proof.

{-# OPTIONS --safe #-}

module mathd-algebra-17 where

open import Agda.Builtin.Int using (Int; pos; negsuc)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)

infix 4 _≤ₙ_
infix 5 _≈ℝ_ _≤ℝ_
infixr 4 _∧_
infixr 3 _∨_

record _∧_ (A B : Set) : Set where
  constructor both
  field
    first  : A
    second : B

data _∨_ (A B : Set) : Set where
  left  : A → A ∨ B
  right : B → A ∨ B

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

ratZero : Rational
ratZero = ratFromNat zero

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

-- Rational Cauchy sequences modulo SequenceEquivalent are the standard real completion.
record Real : Set where
  constructor cauchyReal
  field
    approximation : Sequence
    cauchy         : Cauchy approximation

open Real public

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

_≈ℝ_ : Sequence → Sequence → Set
_≈ℝ_ = SequenceEquivalent

constantSequence : Rational → Sequence
constantSequence q n = q

naturalSequence : Nat → Sequence
naturalSequence n = constantSequence (ratFromNat n)

sequenceAdd : Sequence → Sequence → Sequence
sequenceAdd first second n = ratAdd (first n) (second n)

sequenceMultiply : Sequence → Sequence → Sequence
sequenceMultiply first second n = ratMultiply (first n) (second n)

-- This eventual epsilon order is the usual non-strict order on the Cauchy completion.
_≤ℝ_ : Sequence → Sequence → Set
first ≤ℝ second =
  (precision : Nat) →
  Exists Nat
    (λ cutoff →
      (n : Nat) →
      cutoff ≤ₙ n →
      RationalLessOrEqual
        (first n)
        (ratAdd (second n) (unitFraction precision)))

-- The relation identifies the nonnegative root of a nonnegative real and gives zero on
-- nonpositive inputs, exactly matching the totalized principal square root in the sources.
PrincipalSquareRoot : Sequence → Real → Set
PrincipalSquareRoot x root =
  naturalSequence 0 ≤ℝ approximation root
  ∧
  ((naturalSequence 0 ≤ℝ x
    ∧ sequenceMultiply (approximation root) (approximation root) ≈ℝ x)
   ∨
   (x ≤ℝ naturalSequence 0
    ∧ approximation root ≈ℝ naturalSequence 0))

radicalEquation : Real → Set
radicalEquation a =
  Exists Real λ inner-left →
  Exists Real λ outer-left →
  Exists Real λ inner-right →
  Exists Real λ outer-right →
    PrincipalSquareRoot
      (sequenceAdd
        (naturalSequence 16)
        (sequenceMultiply
          (naturalSequence 16)
          (approximation a)))
      inner-left
    ∧ PrincipalSquareRoot
        (sequenceAdd
          (naturalSequence 4)
          (approximation inner-left))
        outer-left
    ∧ PrincipalSquareRoot
        (sequenceAdd
          (naturalSequence 1)
          (approximation a))
        inner-right
    ∧ PrincipalSquareRoot
        (sequenceAdd
          (naturalSequence 1)
          (approximation inner-right))
        outer-right
    ∧ sequenceAdd
        (approximation outer-left)
        (approximation outer-right)
      ≈ℝ naturalSequence 6

-- All witnesses above remain internal to the hypothesis. Quotient equality, pointwise
-- addition and multiplication, and PrincipalSquareRoot therefore give a bidirectionally
-- equivalent presentation of the source implication over the fixed standard real numbers.
mathd-algebra-17 : Set
mathd-algebra-17 =
  (a : Real) →
  radicalEquation a →
  approximation a ≈ℝ naturalSequence 8
