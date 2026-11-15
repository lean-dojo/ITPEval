-- Statement-only formalization of miniF2F artifact aime_1990_p4: a positive
-- real satisfying a reciprocal equation with three quadratic denominators
-- equals 13. This file contains no proof.

module aime-1990-p4 where

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

data Rational : Set where
  fraction : Int → Nat → Rational

numerator : Rational → Int
numerator (fraction z d) = z

denominator-minus-one : Rational → Nat
denominator-minus-one (fraction z d) = d

denominatorNat : Rational → Nat
denominatorNat q = suc (denominator-minus-one q)

ratNegate : Rational → Rational
ratNegate q =
  fraction (negateInt (numerator q)) (denominator-minus-one q)

ratAdd : Rational → Rational → Rational
ratAdd x y =
  fraction
    (addInt
      (scaleInt (numerator x) (denominatorNat y))
      (scaleInt (numerator y) (denominatorNat x)))
    (pred (denominatorNat x * denominatorNat y))

ratSubtract : Rational → Rational → Rational
ratSubtract x y = ratAdd x (ratNegate y)

ratMultiply : Rational → Rational → Rational
ratMultiply x y =
  fraction
    (multiplyInt (numerator x) (numerator y))
    (pred (denominatorNat x * denominatorNat y))

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
    (scaleInt (numerator x) (denominatorNat y))
    (scaleInt (numerator y) (denominatorNat x))
  where
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

sequenceScale : Nat → Sequence → Sequence
sequenceScale coefficient sequence index =
  ratMultiply (rationalNat coefficient) (sequence index)

sequenceInverse : Sequence → Sequence
sequenceInverse sequence index =
  ratInverse (sequence index)

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

quadraticDenominator : Nat → Real → Sequence
quadraticDenominator constant x =
  sequenceSubtract
    (sequenceSubtract
      (sequenceMultiply
        (approximation x)
        (approximation x))
      (sequenceScale 10 (approximation x)))
    (naturalSequence constant)

reciprocalEquation : Real → Sequence
reciprocalEquation x =
  sequenceSubtract
    (sequenceAdd
      (sequenceInverse (quadraticDenominator 29 x))
      (sequenceInverse (quadraticDenominator 45 x)))
    (sequenceScale 2
      (sequenceInverse (quadraticDenominator 69 x)))

aime-1990-p4 : Set
aime-1990-p4 =
  (x : Real) →
  strictlyPositive x →
  Not
    (SequenceEquivalent
      (quadraticDenominator 29 x)
      (naturalSequence 0)) →
  Not
    (SequenceEquivalent
      (quadraticDenominator 45 x)
      (naturalSequence 0)) →
  Not
    (SequenceEquivalent
      (quadraticDenominator 69 x)
      (naturalSequence 0)) →
  SequenceEquivalent
    (reciprocalEquation x)
    (naturalSequence 0) →
  SequenceEquivalent
    (approximation x)
    (naturalSequence 13)
