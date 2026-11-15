-- Statement-only formalization of miniF2F valid problem mathd_algebra_282:
-- evaluation of a real function defined by rational and irrational branches
-- using floor and ceiling. This file contains no proof.

{-# OPTIONS --safe #-}

module mathd-algebra-282 where

open import Agda.Builtin.Int using (Int; pos; negsuc)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)

infix 4 _≤ₙ_ _≈ℝ_
infixr 3 _∧_
infixl 6 _+ℝ_
infixl 7 _*ℝ_

data ⊥ : Set where

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

successorInt : Int → Int
successorInt (pos n) = pos (suc n)
successorInt (negsuc zero) = pos zero
successorInt (negsuc (suc n)) = negsuc n

predecessorInt : Int → Int
predecessorInt (pos zero) = negsuc zero
predecessorInt (pos (suc n)) = pos n
predecessorInt (negsuc n) = negsuc (suc n)

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

-- A denominator is stored one below its positive mathematical value.
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

ratFromInt : Int → Rational
ratFromInt z = fraction z zero

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

ratInverse : Rational → Rational
ratInverse (fraction (pos zero) d) = fraction (pos zero) zero
ratInverse (fraction (pos (suc n)) d) = fraction (pos (suc d)) n
ratInverse (fraction (negsuc n) d) = fraction (negsuc d) n

ratDivide : Rational → Rational → Rational
ratDivide x y = ratMultiply x (ratInverse y)

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

constantSequence : Rational → Sequence
constantSequence q n = q

naturalSequence : Nat → Sequence
naturalSequence n = constantSequence (ratFromNat n)

integerSequence : Int → Sequence
integerSequence z = constantSequence (ratFromInt z)

_+ℝ_ : Sequence → Sequence → Sequence
(x +ℝ y) n = ratAdd (x n) (y n)

negateReal : Sequence → Sequence
negateReal x n = ratNegate (x n)

_*ℝ_ : Sequence → Sequence → Sequence
(x *ℝ y) n = ratMultiply (x n) (y n)

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

-- Equality in the fixed Cauchy completion of the rationals.
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

record Real : Set where
  constructor cauchyReal
  field
    approximation : Sequence
    cauchy         : Cauchy approximation

open Real public

SequenceLessOrEqual : Sequence → Sequence → Set
SequenceLessOrEqual left right =
  (precision : Nat) →
  Exists Nat
    (λ cutoff →
      (n : Nat) →
      cutoff ≤ₙ n →
      RationalLessOrEqual
        (left n)
        (ratAdd (right n) (unitFraction precision)))

SequenceLessThan : Sequence → Sequence → Set
SequenceLessThan left right =
  Exists Nat
    (λ margin →
      Exists Nat
        (λ cutoff →
          (n : Nat) →
          cutoff ≤ₙ n →
          RationalLessOrEqual
            (ratAdd (left n) (unitFraction margin))
            (right n)))

RationalReal : Sequence → Set
RationalReal x =
  Exists Rational (λ q → x ≈ℝ constantSequence q)

IrrationalReal : Sequence → Set
IrrationalReal x = RationalReal x → ⊥

Floor : Sequence → Int → Set
Floor x z =
  SequenceLessOrEqual (integerSequence z) x
  ∧
  SequenceLessThan x (integerSequence (successorInt z))

Ceiling : Sequence → Int → Set
Ceiling x z =
  SequenceLessThan (integerSequence (predecessorInt z)) x
  ∧
  SequenceLessOrEqual x (integerSequence z)

absoluteIntegerSequence : Int → Sequence
absoluteIntegerSequence z = naturalSequence (absoluteInt z)

squareIntegerSequence : Int → Sequence
squareIntegerSequence z = integerSequence z *ℝ integerSequence z

alternatingOne : Nat → Int
alternatingOne zero = pos 1
alternatingOne (suc n) = negateInt (alternatingOne n)

leibnizTerm : Nat → Rational
leibnizTerm n = fraction (alternatingOne n) (n + n)

leibnizPartialSum : Nat → Rational
leibnizPartialSum zero = leibnizTerm zero
leibnizPartialSum (suc n) =
  ratAdd (leibnizPartialSum n) (leibnizTerm (suc n))

-- Four times the Gregory-Leibniz series is a fixed representative of pi.
piSequence : Sequence
piSequence n =
  ratMultiply (ratFromNat 4) (leibnizPartialSum n)

Nonnegative : Real → Set
Nonnegative x =
  SequenceLessOrEqual
    (naturalSequence 0)
    (approximation x)

CubeRootEight : Real → Set
CubeRootEight x =
  Nonnegative x
  ∧
  ((approximation x *ℝ approximation x) *ℝ approximation x)
    ≈ℝ naturalSequence 8

SquareRootFifty : Real → Set
SquareRootFifty x =
  Nonnegative x
  ∧
  (approximation x *ℝ approximation x)
    ≈ℝ naturalSequence 50

NegativePi : Real → Set
NegativePi x =
  approximation x ≈ℝ negateReal piSequence

NineHalves : Real → Set
NineHalves x =
  approximation x
    ≈ℝ constantSequence (fraction (pos 9) 1)

record RealFunction : Set where
  field
    apply :
      Real →
      Real
    respects-real-equality :
      (x y : Real) →
      approximation x ≈ℝ approximation y →
      approximation (apply x) ≈ℝ approximation (apply y)

open RealFunction public

fourTermValue : RealFunction → Real → Real → Real → Real → Sequence
fourTermValue f cube-root-eight negative-pi square-root-fifty nine-halves =
  ((approximation (apply f cube-root-eight)
      +ℝ approximation (apply f negative-pi))
    +ℝ approximation (apply f square-root-fifty))
  +ℝ approximation (apply f nine-halves)

mathd-algebra-282 : Set
mathd-algebra-282 =
  (f : RealFunction) →
  ((x : Real) →
    RationalReal (approximation x) →
    (z : Int) →
    Floor (approximation x) z →
    approximation (apply f x) ≈ℝ absoluteIntegerSequence z) →
  ((x : Real) →
    IrrationalReal (approximation x) →
    (z : Int) →
    Ceiling (approximation x) z →
    approximation (apply f x) ≈ℝ squareIntegerSequence z) →
  (cube-root-eight negative-pi square-root-fifty nine-halves : Real) →
  CubeRootEight cube-root-eight →
  NegativePi negative-pi →
  SquareRootFifty square-root-fifty →
  NineHalves nine-halves →
  fourTermValue
    f
    cube-root-eight
    negative-pi
    square-root-fifty
    nine-halves
  ≈ℝ naturalSequence 79
