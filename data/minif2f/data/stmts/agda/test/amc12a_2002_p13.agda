-- Statement-only formalization of miniF2F test artifact amc12a_2002_p13:
-- two distinct positive real numbers satisfying absolute reciprocal-difference
-- equations sum to the nonnegative square root of five, using rational Cauchy
-- sequences for the standard real numbers. This file contains no proof.

module amc12a-2002-p13 where

open import Agda.Builtin.Int using (Int; pos; negsuc)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)

infix 4 _≤ₙ_
infixr 4 _∧_

data ⊥ : Set where

Not : Set → Set
Not A = A → ⊥

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

data Rational : Set where
  fraction : Int → Nat → Rational

numerator : Rational → Int
numerator (fraction z d) = z

denominator-minus-one : Rational → Nat
denominator-minus-one (fraction z d) = d

denominator : Rational → Nat
denominator q = suc (denominator-minus-one q)

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

ratAbsolute : Rational → Rational
ratAbsolute q =
  fraction
    (pos (absoluteInt (numerator q)))
    (denominator-minus-one q)

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

rationalNat : Nat → Rational
rationalNat n = fraction (pos n) zero

unitFraction : Nat → Rational
unitFraction n = fraction (pos 1) n

Sequence : Set
Sequence = Nat → Rational

naturalSequence : Nat → Sequence
naturalSequence n index = rationalNat n

sequenceAdd : Sequence → Sequence → Sequence
sequenceAdd left right index =
  ratAdd (left index) (right index)

sequenceSubtract : Sequence → Sequence → Sequence
sequenceSubtract left right index =
  ratSubtract (left index) (right index)

sequenceMultiply : Sequence → Sequence → Sequence
sequenceMultiply left right index =
  ratMultiply (left index) (right index)

sequenceInverse : Sequence → Sequence
sequenceInverse sequence index =
  ratInverse (sequence index)

sequenceAbsolute : Sequence → Sequence
sequenceAbsolute sequence index =
  ratAbsolute (sequence index)

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

strictlyPositive : Real → Set
strictlyPositive x =
  SequenceLessThan
    (naturalSequence 0)
    (approximation x)

distinct : Real → Real → Set
distinct x y =
  Not
    (SequenceEquivalent
      (approximation x)
      (approximation y))

reciprocalDifference : Real → Sequence
reciprocalDifference x =
  sequenceSubtract
    (approximation x)
    (sequenceInverse (approximation x))

absoluteReciprocalEquation : Real → Set
absoluteReciprocalEquation x =
  SequenceEquivalent
    (sequenceAbsolute (reciprocalDifference x))
    (naturalSequence 1)

NonnegativeSquareRootOf : Sequence → Sequence → Set
NonnegativeSquareRootOf root radicand =
  SequenceLessOrEqual
    (naturalSequence 0)
    root
  ∧
  SequenceEquivalent
    (sequenceMultiply root root)
    radicand

amc12a-2002-p13 : Set
amc12a-2002-p13 =
  (a b : Real) →
  strictlyPositive a →
  strictlyPositive b →
  distinct a b →
  absoluteReciprocalEquation a →
  absoluteReciprocalEquation b →
  NonnegativeSquareRootOf
    (sequenceAdd
      (approximation a)
      (approximation b))
    (naturalSequence 5)
