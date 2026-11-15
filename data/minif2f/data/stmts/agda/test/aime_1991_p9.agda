-- Statement-only formalization of miniF2F artifact aime_1991_p9: a
-- trigonometric equation determines a reduced rational whose numerator and
-- denominator sum to 44. This file contains no proof.

module aime-1991-p9 where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Int using (Int; pos; negsuc)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)

infix 4 _≤ₙ_
infixl 6 _+z_
infixl 7 _*z_

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

_+z_ : Int → Int → Int
pos m +z pos n = pos (m + n)
pos m +z negsuc n = difference m (suc n)
negsuc m +z pos n = difference n (suc m)
negsuc m +z negsuc n = negsuc (suc (m + n))

_*z_ : Int → Int → Int
pos m *z pos n = pos (m * n)
pos m *z negsuc n = negative (m * suc n)
negsuc m *z pos n = negative (suc m * n)
negsuc m *z negsuc n = pos (suc m * suc n)

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
    ((numerator x *z pos (denominator y)) +z
     (numerator y *z pos (denominator x)))
    (pred (denominator x * denominator y))

ratMultiply : Rational → Rational → Rational
ratMultiply x y =
  fraction
    (numerator x *z numerator y)
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

ratSubtract : Rational → Rational → Rational
ratSubtract x y = ratAdd x (ratNegate y)

rationalNat : Nat → Rational
rationalNat n = fraction (pos n) zero

unitFraction : Nat → Rational
unitFraction n = fraction (pos 1) n

ratDivideByNat : Rational → Nat → Rational
ratDivideByNat q n =
  fraction
    (numerator q)
    (pred (denominator q * n))

RationalLessOrEqual : Rational → Rational → Set
RationalLessOrEqual x y =
  IntLessOrEqual
    (numerator x *z pos (denominator y))
    (numerator y *z pos (denominator x))
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
constantSequence q n = q

sequenceAdd : Sequence → Sequence → Sequence
sequenceAdd left right n = ratAdd (left n) (right n)

sequenceMultiply : Sequence → Sequence → Sequence
sequenceMultiply left right n = ratMultiply (left n) (right n)

sequenceInverse : Sequence → Sequence
sequenceInverse sequence n = ratInverse (sequence n)

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
sinePartial q (suc n) = ratAdd (sinePartial q n) (sineTerm q n)

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

tangentSequence : Real → Sequence
tangentSequence x =
  sequenceMultiply
    (sineSequence x)
    (sequenceInverse (cosineSequence x))

secantPlusTangent : Real → Sequence
secantPlusTangent x =
  sequenceAdd
    (sequenceInverse (cosineSequence x))
    (tangentSequence x)

cosecantPlusCotangent : Real → Sequence
cosecantPlusCotangent x =
  sequenceAdd
    (sequenceInverse (sineSequence x))
    (sequenceInverse (tangentSequence x))

record Coprime (a : Int) (b : Nat) : Set where
  constructor bezout
  field
    left-coefficient right-coefficient : Int
    combination :
      (left-coefficient *z a) +z
      (right-coefficient *z pos b) ≡ pos 1

record ReducedRational : Set where
  constructor reducedFraction
  field
    reducedNumerator : Int
    reducedDenominatorMinusOne : Nat
    reduced :
      Coprime reducedNumerator (suc reducedDenominatorMinusOne)

reducedDenominator : ReducedRational → Nat
reducedDenominator q =
  suc (ReducedRational.reducedDenominatorMinusOne q)

asRational : ReducedRational → Rational
asRational q =
  fraction
    (ReducedRational.reducedNumerator q)
    (ReducedRational.reducedDenominatorMinusOne q)

twentyTwoSevenths : Sequence
twentyTwoSevenths =
  constantSequence (fraction (pos 22) 6)

reducedRationalSequence : ReducedRational → Sequence
reducedRationalSequence q =
  constantSequence (asRational q)

numeratorPlusDenominator : ReducedRational → Int
numeratorPlusDenominator q =
  ReducedRational.reducedNumerator q +z
  pos (reducedDenominator q)

aime-1991-p9 : Set
aime-1991-p9 =
  (x : Real) →
  (m : ReducedRational) →
  SequenceEquivalent
    (secantPlusTangent x)
    twentyTwoSevenths →
  SequenceEquivalent
    (cosecantPlusCotangent x)
    (reducedRationalSequence m) →
  numeratorPlusDenominator m ≡ pos 44
