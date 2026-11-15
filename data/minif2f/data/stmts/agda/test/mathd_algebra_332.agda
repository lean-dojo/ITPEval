-- Statement-only formalization of miniF2F test problem mathd_algebra_332: two real numbers
-- with arithmetic mean 7 and equal principal square roots of their product and 19 have sum
-- of squares 158. Rational Cauchy sequences represent the standard reals. This file contains
-- no proof.

{-# OPTIONS --safe #-}

module mathd-algebra-332 where

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

halfRational : Rational
halfRational = fraction (pos 1) (suc zero)

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

-- Rational Cauchy sequences modulo _≈ℝ_ are the standard real numbers.
record Real : Set where
  constructor cauchyReal
  field
    approximation : Sequence
    cauchy         : Cauchy approximation

open Real public

_≈ℝ_ : Sequence → Sequence → Set
first ≈ℝ second =
  (precision : Nat) →
  Exists Nat
    (λ cutoff →
      (n : Nat) →
      cutoff ≤ₙ n →
      RationalDistanceWithin
        (first n)
        (second n)
        (unitFraction precision))

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

constantSequence : Rational → Sequence
constantSequence q n = q

naturalSequence : Nat → Sequence
naturalSequence n = constantSequence (ratFromNat n)

sequenceAdd : Sequence → Sequence → Sequence
sequenceAdd first second n = ratAdd (first n) (second n)

sequenceMultiply : Sequence → Sequence → Sequence
sequenceMultiply first second n = ratMultiply (first n) (second n)

sequenceHalf : Sequence → Sequence
sequenceHalf sequence n = ratMultiply (sequence n) halfRational

-- This relation is the totalized principal square root: the nonnegative root on
-- nonnegative inputs and zero on nonpositive inputs.
PrincipalSquareRoot : Sequence → Real → Set
PrincipalSquareRoot radicand root =
  naturalSequence 0 ≤ℝ approximation root
  ∧
  ((naturalSequence 0 ≤ℝ radicand
    ∧ sequenceMultiply
        (approximation root)
        (approximation root)
      ≈ℝ radicand)
   ∨
   (radicand ≤ℝ naturalSequence 0
    ∧ approximation root ≈ℝ naturalSequence 0))

SquareRootsEqual : Sequence → Sequence → Set
SquareRootsEqual first second =
  Exists Real λ firstRoot →
  Exists Real λ secondRoot →
    PrincipalSquareRoot first firstRoot
    ∧ PrincipalSquareRoot second secondRoot
    ∧ approximation firstRoot ≈ℝ approximation secondRoot

mathd-algebra-332 : Set
mathd-algebra-332 =
  (x y : Real) →
  sequenceHalf
    (sequenceAdd
      (approximation x)
      (approximation y))
    ≈ℝ naturalSequence 7 →
  SquareRootsEqual
    (sequenceMultiply
      (approximation x)
      (approximation y))
    (naturalSequence 19) →
  sequenceAdd
    (sequenceMultiply
      (approximation x)
      (approximation x))
    (sequenceMultiply
      (approximation y)
      (approximation y))
    ≈ℝ naturalSequence 158
