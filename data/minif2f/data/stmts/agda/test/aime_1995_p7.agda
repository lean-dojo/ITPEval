-- Statement-only formalization of miniF2F artifact aime_1995_p7: two
-- trigonometric equations determine positive coprime naturals whose sum is
-- 27, using rational Cauchy sequences for the real numbers. This file contains
-- no proof.

module aime-1995-p7 where

open import Agda.Builtin.Bool using (true; false)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Int using (Int; pos; negsuc)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_; _<_)

infix 4 _≤ₙ_

record Exists (A : Set) (P : A → Set) : Set where
  constructor witness
  field
    value    : A
    property : P value

data _≤ₙ_ : Nat → Nat → Set where
  zero≤   : {n : Nat} → zero ≤ₙ n
  suc≤suc : {m n : Nat} → m ≤ₙ n → suc m ≤ₙ suc n

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

ratAbsolute : Rational → Rational
ratAbsolute q =
  fraction
    (pos (absoluteInt (numerator q)))
    (denominator-minus-one q)

ratDivideByNat : Rational → Nat → Rational
ratDivideByNat q n =
  fraction
    (numerator q)
    (pred (denominator q * n))

RationalLessOrEqual : Rational → Rational → Set
RationalLessOrEqual x y =
  IntLessOrEqual
    (scaleInt (numerator x) (denominator y))
    (scaleInt (numerator y) (denominator x))
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

Sequence : Set
Sequence = Nat → Rational

constantSequence : Rational → Sequence
constantSequence q index = q

naturalSequence : Nat → Sequence
naturalSequence n = constantSequence (rationalNat n)

ratioSequence : Nat → Nat → Sequence
ratioSequence p q =
  constantSequence (fraction (pos p) (pred q))

sequenceAdd : Sequence → Sequence → Sequence
sequenceAdd left right index =
  ratAdd (left index) (right index)

sequenceSubtract : Sequence → Sequence → Sequence
sequenceSubtract left right index =
  ratSubtract (left index) (right index)

sequenceMultiply : Sequence → Sequence → Sequence
sequenceMultiply left right index =
  ratMultiply (left index) (right index)

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

factorial : Nat → Nat
factorial zero = 1
factorial (suc n) = suc n * factorial n

ratPower : Rational → Nat → Rational
ratPower q zero = rationalNat 1
ratPower q (suc n) = ratMultiply q (ratPower q n)

alternateSign : Nat → Rational → Rational
alternateSign zero q = q
alternateSign (suc n) q = ratNegate (alternateSign n q)

sineTerm : Rational → Nat → Rational
sineTerm q n =
  alternateSign n
    (ratDivideByNat
      (ratPower q (suc (n + n)))
      (factorial (suc (n + n))))

cosineTerm : Rational → Nat → Rational
cosineTerm q n =
  alternateSign n
    (ratDivideByNat
      (ratPower q (n + n))
      (factorial (n + n)))

sinePartial : Rational → Nat → Rational
sinePartial q zero = rationalNat 0
sinePartial q (suc n) =
  ratAdd (sinePartial q n) (sineTerm q n)

cosinePartial : Rational → Nat → Rational
cosinePartial q zero = rationalNat 0
cosinePartial q (suc n) =
  ratAdd (cosinePartial q n) (cosineTerm q n)

sineSequence : Real → Sequence
sineSequence x n =
  sinePartial (approximation x n) (suc n)

cosineSequence : Real → Sequence
cosineSequence x n =
  cosinePartial (approximation x n) (suc n)

boundedFloorSquareRoot : Nat → Nat → Nat
boundedFloorSquareRoot target zero = zero
boundedFloorSquareRoot target (suc bound)
  with (suc bound * suc bound) < suc target
... | true = suc bound
... | false = boundedFloorSquareRoot target bound

squareRootApproximation : Nat → Nat → Rational
squareRootApproximation k precision =
  fraction
    (pos
      (boundedFloorSquareRoot
        (k * (d * d))
        (k * d)))
    precision
  where
    d = suc precision

squareRootSequence : Nat → Sequence
squareRootSequence k precision =
  squareRootApproximation k precision

onePlus : Sequence → Sequence
onePlus sequence =
  sequenceAdd (naturalSequence 1) sequence

oneMinus : Sequence → Sequence
oneMinus sequence =
  sequenceSubtract (naturalSequence 1) sequence

firstEquation : Real → Set
firstEquation t =
  SequenceEquivalent
    (sequenceMultiply
      (onePlus (sineSequence t))
      (onePlus (cosineSequence t)))
    (ratioSequence 5 4)

secondEquation : Nat → Nat → Nat → Real → Set
secondEquation k m n t =
  SequenceEquivalent
    (sequenceMultiply
      (oneMinus (sineSequence t))
      (oneMinus (cosineSequence t)))
    (sequenceSubtract
      (ratioSequence m n)
      (squareRootSequence k))

aime-1995-p7 : Set
aime-1995-p7 =
  (k m n : Nat) →
  (t : Real) →
  Positive k →
  Positive m →
  Positive n →
  Coprime m n →
  firstEquation t →
  secondEquation k m n t →
  k + m + n ≡ 27
