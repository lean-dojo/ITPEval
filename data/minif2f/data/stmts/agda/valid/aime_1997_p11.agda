-- Statement-only formalization of miniF2F valid problem aime_1997_p11: the floor of 100
-- times the ratio of the cosine and sine sums for degree angles 1 through 44 is 241,
-- using rational Cauchy sequences for the real numbers. This file contains no proof.

module aime-1997-p11 where

open import Agda.Builtin.Equality using (_≡_)
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

ratFromNat : Nat → Rational
ratFromNat n = ratFromInt (pos n)

ratZero ratOne ratFour : Rational
ratZero = ratFromNat 0
ratOne = ratFromNat 1
ratFour = ratFromNat 4

unitFraction : Nat → Rational
unitFraction n = fraction (pos 1) n

ratNegate : Rational → Rational
ratNegate q =
  fraction (negateInt (numerator q)) (denominator-minus-one q)

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
ratInverse q with numerator q
... | pos zero = ratZero
... | pos (suc n) = fraction (pos (denominator q)) n
... | negsuc n = fraction (negative (denominator q)) n

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

scaleSequence : Nat → Sequence → Sequence
scaleSequence factor sequence n =
  ratMultiply (ratFromNat factor) (sequence n)

IsFloor : Sequence → Int → Set
IsFloor sequence z =
  SequenceLessOrEqual
    (constantSequence (ratFromInt z))
    sequence
  ∧
  SequenceStrictLess
    sequence
    (constantSequence (ratFromInt (successorInt z)))

alternatingSign : Nat → Int
alternatingSign zero = pos 1
alternatingSign (suc n) = negateInt (alternatingSign n)

factorial : Nat → Nat
factorial zero = 1
factorial (suc n) = suc n * factorial n

ratPower : Rational → Nat → Rational
ratPower x zero = ratOne
ratPower x (suc n) = ratMultiply (ratPower x n) x

sumThrough : Nat → (Nat → Rational) → Rational
sumThrough zero term = term zero
sumThrough (suc n) term =
  ratAdd (sumThrough n term) (term (suc n))

odd : Nat → Nat
odd n = suc (n + n)

leibnizTerm : Nat → Rational
leibnizTerm n =
  fraction
    (alternatingSign n)
    (pred (odd n))

piApproximation : Sequence
piApproximation n =
  ratMultiply ratFour (sumThrough n leibnizTerm)

sineTerm : Rational → Nat → Rational
sineTerm x n =
  ratMultiply
    (ratFromInt (alternatingSign n))
    (ratDivide
      (ratPower x (odd n))
      (ratFromNat (factorial (odd n))))

cosineTerm : Rational → Nat → Rational
cosineTerm x n =
  ratMultiply
    (ratFromInt (alternatingSign n))
    (ratDivide
      (ratPower x (n + n))
      (ratFromNat (factorial (n + n))))

sineApproximation : Nat → Rational → Rational
sineApproximation precision x =
  sumThrough precision (sineTerm x)

cosineApproximation : Nat → Rational → Rational
cosineApproximation precision x =
  sumThrough precision (cosineTerm x)

degreeApproximation : Nat → Nat → Rational
degreeApproximation precision degree =
  ratDivide
    (ratMultiply
      (ratFromNat degree)
      (piApproximation precision))
    (ratFromNat 180)

sineDegreeSequence : Nat → Sequence
sineDegreeSequence degree precision =
  sineApproximation precision
    (degreeApproximation precision degree)

cosineDegreeSequence : Nat → Sequence
cosineDegreeSequence degree precision =
  cosineApproximation precision
    (degreeApproximation precision degree)

sumFromOne : Nat → (Nat → Rational) → Rational
sumFromOne zero term = ratZero
sumFromOne (suc n) term =
  ratAdd (sumFromOne n term) (term (suc n))

sineSumSequence : Sequence
sineSumSequence precision =
  sumFromOne 44
    (λ degree → sineDegreeSequence degree precision)

cosineSumSequence : Sequence
cosineSumSequence precision =
  sumFromOne 44
    (λ degree → cosineDegreeSequence degree precision)

trigonometricQuotientSequence : Sequence
trigonometricQuotientSequence precision =
  ratDivide
    (cosineSumSequence precision)
    (sineSumSequence precision)

Aime1997P11 : Set
Aime1997P11 =
  (x : Real) →
  SequenceEquivalent
    (approximation x)
    trigonometricQuotientSequence →
  IsFloor
    (scaleSequence 100 (approximation x))
    (pos 241)
