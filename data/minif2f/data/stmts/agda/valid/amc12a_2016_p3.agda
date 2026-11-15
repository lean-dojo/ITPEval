-- Statement-only formalization of miniF2F valid problem amc12a_2016_p3 using exact
-- rational Cauchy-sequence reals: evaluating a floor-based remainder function at
-- 3/8 and -2/5. This file contains no proof.

module amc12a-2016-p3 where

open import Agda.Builtin.Int using (Int; pos; negsuc)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)

infix 4 _≤ₙ_
infixr 4 _∧_
infixr 3 _∨_

record _∧_ (A B : Set) : Set where
  constructor both
  field
    first  : A
    second : B

data _∨_ (A B : Set) : Set where
  or-left  : A → A ∨ B
  or-right : B → A ∨ B

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

successorInt : Int → Int
successorInt z = addInt z (pos 1)

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

-- SequenceEquivalent is equality in the Cauchy completion of the rationals.
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

constantSequence : Rational → Sequence
constantSequence q n = q

zeroSequence : Sequence
zeroSequence = constantSequence (ratFromInt (pos zero))

sequenceScaleByInt : Sequence → Int → Sequence
sequenceScaleByInt sequence z n =
  ratMultiply (sequence n) (ratFromInt z)

sequenceSubtract : Sequence → Sequence → Sequence
sequenceSubtract left right n =
  ratSubtract (left n) (right n)

remainderSequence : Sequence → Sequence → Int → Sequence
remainderSequence x y z =
  sequenceSubtract x (sequenceScaleByInt y z)

-- Apartness from zero is equivalent to inequality for the classical real line.
SequenceApartFromZero : Sequence → Set
SequenceApartFromZero sequence =
  SequenceStrictLess zeroSequence sequence ∨
  SequenceStrictLess sequence zeroSequence

-- These two constructors are the sign-aware cross-multiplied characterization
-- z ≤ x / y < z + 1, so they define z = floor (x / y) without choosing a
-- representative-level reciprocal.
data QuotientFloor
  (x y : Sequence)
  (z : Int) : Set where
  positive-denominator :
    SequenceStrictLess zeroSequence y →
    SequenceLessOrEqual
      (sequenceScaleByInt y z)
      x →
    SequenceStrictLess
      x
      (sequenceScaleByInt y (successorInt z)) →
    QuotientFloor x y z
  negative-denominator :
    SequenceStrictLess y zeroSequence →
    SequenceStrictLess
      (sequenceScaleByInt y (successorInt z))
      x →
    SequenceLessOrEqual
      x
      (sequenceScaleByInt y z) →
    QuotientFloor x y z

-- A total extensional functional relation is exactly a function on Cauchy
-- sequences modulo SequenceEquivalent, without selecting representatives.
record RealFunction
  (F : Sequence → Sequence → Sequence → Set) : Set₁ where
  field
    output-real :
      (x y result : Sequence) →
      Cauchy x →
      Cauchy y →
      F x y result →
      Cauchy result
    total :
      (x y : Sequence) →
      Cauchy x →
      Cauchy y →
      Exists Sequence
        (λ result →
          Cauchy result ∧
          F x y result)
    congruent :
      (x x′ y y′ result result′ : Sequence) →
      Cauchy x →
      Cauchy x′ →
      Cauchy y →
      Cauchy y′ →
      SequenceEquivalent x x′ →
      SequenceEquivalent y y′ →
      F x y result →
      F x′ y′ result′ →
      SequenceEquivalent result result′

threeEighths negativeTwoFifths negativeOneFortieth : Rational
threeEighths = fraction (pos 3) 7
negativeTwoFifths = fraction (negsuc 1) 4
negativeOneFortieth = fraction (negsuc 0) 39

amc12a-2016-p3 : Set₁
amc12a-2016-p3 =
  (F : Sequence → Sequence → Sequence → Set) →
  RealFunction F →
  ((x y result : Sequence) →
    Cauchy x →
    Cauchy y →
    SequenceApartFromZero y →
    F x y result →
    (z : Int) →
    QuotientFloor x y z →
    SequenceEquivalent
      result
      (remainderSequence x y z)) →
  (result : Sequence) →
  F
    (constantSequence threeEighths)
    (constantSequence negativeTwoFifths)
    result →
  SequenceEquivalent
    result
    (constantSequence negativeOneFortieth)
