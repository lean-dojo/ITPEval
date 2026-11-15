-- Statement-only formalization of miniF2F test problem mathd_algebra_293:
-- for every nonnegative real x, the product sqrt(60x) sqrt(12x) sqrt(63x)
-- equals 36x sqrt(35x). This file contains no proof.

{-# OPTIONS --safe #-}

module mathd-algebra-293 where

open import Agda.Builtin.Int using (Int; pos; negsuc)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)

infix 4 _≤ₙ_ _≤ℝ_ _≈ℝ_
infixr 2 _∧_

record _∧_ (A B : Set) : Set where
  constructor _,_
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
-- The relations below are invariant under that quotient and therefore denote
-- the standard order, arithmetic, and nonnegative square root.
record Real : Set where
  constructor cauchyReal
  field
    approximation : Sequence
    cauchy         : Cauchy approximation

open Real public

_≈ℝ_ : Sequence → Sequence → Set
left ≈ℝ right =
  (precision : Nat) →
  Exists Nat
    (λ cutoff →
      (n : Nat) →
      cutoff ≤ₙ n →
      RationalDistanceWithin
        (left n)
        (right n)
        (unitFraction precision))

_≤ℝ_ : Sequence → Sequence → Set
left ≤ℝ right =
  (precision : Nat) →
  Exists Nat
    (λ cutoff →
      (n : Nat) →
      cutoff ≤ₙ n →
      RationalLessOrEqual
        (left n)
        (ratAdd (right n) (unitFraction precision)))

constantSequence : Rational → Sequence
constantSequence q n = q

naturalSequence : Nat → Sequence
naturalSequence n = constantSequence (ratFromNat n)

sequenceMultiply : Sequence → Sequence → Sequence
sequenceMultiply left right n =
  ratMultiply (left n) (right n)

scaledSequence : Nat → Sequence → Sequence
scaledSequence n sequence =
  sequenceMultiply (naturalSequence n) sequence

Nonnegative : Real → Set
Nonnegative x =
  naturalSequence 0 ≤ℝ approximation x

SquareRootOf : Sequence → Real → Set
SquareRootOf radicand root =
  Nonnegative root ∧
  sequenceMultiply
    (approximation root)
    (approximation root)
  ≈ℝ radicand

radicalProduct : Real → Real → Real → Sequence
radicalProduct root60 root12 root63 =
  sequenceMultiply
    (sequenceMultiply
      (approximation root60)
      (approximation root12))
    (approximation root63)

rightHandSide : Real → Real → Sequence
rightHandSide x root35 =
  sequenceMultiply
    (scaledSequence 36 (approximation x))
    (approximation root35)

mathd-algebra-293 : Set
mathd-algebra-293 =
  (x : Real) →
  Nonnegative x →
  Exists Real λ root60 →
  Exists Real λ root12 →
  Exists Real λ root63 →
  Exists Real λ root35 →
    SquareRootOf
      (scaledSequence 60 (approximation x))
      root60 ∧
    SquareRootOf
      (scaledSequence 12 (approximation x))
      root12 ∧
    SquareRootOf
      (scaledSequence 63 (approximation x))
      root63 ∧
    SquareRootOf
      (scaledSequence 35 (approximation x))
      root35 ∧
    radicalProduct root60 root12 root63
      ≈ℝ rightHandSide x root35
