-- Statement-only formalization of miniF2F test problem aime_1999_p11: a finite
-- trigonometric sum determines a positive reduced rational angle below 90 degrees.
-- This file contains no proof.

module aime-1999-p11 where

open import Agda.Builtin.Bool using (true)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Int using (Int; pos; negsuc)
open import Agda.Builtin.Nat using
  (Nat; zero; suc; _+_; _*_; _<_)

infix 4 _≤ₙ_

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

ratZero : Rational
ratZero = fraction (pos zero) zero

ratOne : Rational
ratOne = fraction (pos 1) zero

rationalNat : Nat → Rational
rationalNat n = fraction (pos n) zero

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
ratInverse (fraction (pos zero) d) = ratZero
ratInverse (fraction (pos (suc n)) d) =
  fraction (pos (suc d)) n
ratInverse (fraction (negsuc n) d) =
  fraction (negsuc d) n

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

alternatingSign : Nat → Int
alternatingSign zero = pos 1
alternatingSign (suc n) = negateInt (alternatingSign n)

oddNatural : Nat → Nat
oddNatural n = suc (n + n)

evenNatural : Nat → Nat
evenNatural n = n + n

factorial : Nat → Nat
factorial zero = 1
factorial (suc n) = suc n * factorial n

ratPower : Rational → Nat → Rational
ratPower x zero = ratOne
ratPower x (suc n) = ratMultiply (ratPower x n) x

signedUnit : Nat → Rational
signedUnit n = fraction (alternatingSign n) zero

leibnizTerm : Nat → Rational
leibnizTerm n =
  fraction
    (alternatingSign n)
    (pred (oddNatural n))

leibnizPartialSum : Nat → Rational
leibnizPartialSum zero = leibnizTerm zero
leibnizPartialSum (suc n) =
  ratAdd
    (leibnizPartialSum n)
    (leibnizTerm (suc n))

piSequence : Sequence
piSequence n =
  ratMultiply
    (rationalNat 4)
    (leibnizPartialSum n)

sineTerm : Rational → Nat → Rational
sineTerm x n =
  ratMultiply
    (signedUnit n)
    (ratDivide
      (ratPower x (oddNatural n))
      (rationalNat (factorial (oddNatural n))))

cosineTerm : Rational → Nat → Rational
cosineTerm x n =
  ratMultiply
    (signedUnit n)
    (ratDivide
      (ratPower x (evenNatural n))
      (rationalNat (factorial (evenNatural n))))

sinePartialSum : Rational → Nat → Rational
sinePartialSum x zero = sineTerm x zero
sinePartialSum x (suc n) =
  ratAdd
    (sinePartialSum x n)
    (sineTerm x (suc n))

cosinePartialSum : Rational → Nat → Rational
cosinePartialSum x zero = cosineTerm x zero
cosinePartialSum x (suc n) =
  ratAdd
    (cosinePartialSum x n)
    (cosineTerm x (suc n))

degreeAngleSequence : Nat → Sequence
degreeAngleSequence k n =
  ratDivide
    (ratMultiply
      (rationalNat (5 * k))
      (piSequence n))
    (rationalNat 180)

rationalAngleSequence : Nat → Nat → Sequence
rationalAngleSequence numerator denominator n =
  ratDivide
    (ratMultiply
      (ratDivide
        (rationalNat numerator)
        (rationalNat denominator))
      (piSequence n))
    (rationalNat 180)

sineSequence : Sequence → Sequence
sineSequence angle n =
  sinePartialSum (angle n) n

cosineSequence : Sequence → Sequence
cosineSequence angle n =
  cosinePartialSum (angle n) n

tangentSequence : Sequence → Sequence
tangentSequence angle n =
  ratDivide
    (sineSequence angle n)
    (cosineSequence angle n)

sumSinesFromOne : Nat → Sequence
sumSinesFromOne zero n = ratZero
sumSinesFromOne (suc k) n =
  ratAdd
    (sumSinesFromOne k n)
    (sineSequence (degreeAngleSequence (suc k)) n)

record Divides (d n : Nat) : Set where
  field
    quotient : Nat
    product  : d * quotient ≡ n

Positive : Nat → Set
Positive n = (zero < n) ≡ true

Coprime : Nat → Nat → Set
Coprime m n =
  (d : Nat) →
  Divides d m →
  Divides d n →
  d ≡ 1

aime-1999-p11 : Set
aime-1999-p11 =
  (m n : Nat) →
  Positive m →
  Positive n →
  SequenceEquivalent
    (sumSinesFromOne 35)
    (tangentSequence (rationalAngleSequence m n)) →
  Coprime m n →
  (m < 90 * n) ≡ true →
  m + n ≡ 177
