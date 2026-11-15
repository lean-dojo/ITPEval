-- Statement-only formalization of miniF2F test artifact amc12a_2021_p22: a
-- monic real cubic with zeros cos(2*pi/7), cos(4*pi/7), and cos(6*pi/7) has
-- coefficient product 1/32. This file contains no proof.

module amc12a-2021-p22 where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Int using (Int; pos; negsuc)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)

infix 4 _≤ₙ_ _≈ᴿ_
infixr 3 _∧_
infixr 2 _∨_
infix 2 _↔_

data ⊥ : Set where

record _∧_ (A B : Set) : Set where
  constructor conjunction
  field
    left  : A
    right : B

data _∨_ (A B : Set) : Set where
  left  : A → A ∨ B
  right : B → A ∨ B

record _↔_ (A B : Set) : Set where
  field
    forward  : A → B
    backward : B → A

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

rationalNat : Nat → Rational
rationalNat n = fraction (pos n) zero

unitFraction : Nat → Rational
unitFraction n = fraction (pos 1) n

ratio : Nat → Nat → Rational
ratio p q = fraction (pos p) (pred q)

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

ratScale : Nat → Rational → Rational
ratScale n q =
  fraction
    (scaleInt (numerator q) n)
    (denominator-minus-one q)

ratDivideByNat : Rational → Nat → Rational
ratDivideByNat q n =
  fraction
    (numerator q)
    (pred (denominator q * n))

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
constantSequence q _ = q

naturalSequence : Nat → Sequence
naturalSequence n = constantSequence (rationalNat n)

ratioSequence : Nat → Nat → Sequence
ratioSequence p q = constantSequence (ratio p q)

sequenceAdd : Sequence → Sequence → Sequence
sequenceAdd first second index =
  ratAdd (first index) (second index)

sequenceMultiply : Sequence → Sequence → Sequence
sequenceMultiply first second index =
  ratMultiply (first index) (second index)

sequenceScale : Nat → Sequence → Sequence
sequenceScale n sequence index =
  ratScale n (sequence index)

sequenceDivideByNat : Sequence → Nat → Sequence
sequenceDivideByNat sequence n index =
  ratDivideByNat (sequence index) n

sequencePower : Sequence → Nat → Sequence
sequencePower sequence zero = naturalSequence 1
sequencePower sequence (suc n) =
  sequenceMultiply sequence (sequencePower sequence n)

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
SequenceEquivalent first second =
  (precision : Nat) →
  Exists Nat
    (λ cutoff →
      (n : Nat) →
      cutoff ≤ₙ n →
      RationalDistanceWithin
        (first n)
        (second n)
        (unitFraction precision))

_≈ᴿ_ : Real → Real → Set
x ≈ᴿ y =
  SequenceEquivalent
    (approximation x)
    (approximation y)

record RealFunction : Set where
  field
    apply : Real → Real
    respects-equivalence :
      (x y : Real) →
      x ≈ᴿ y →
      apply x ≈ᴿ apply y

open RealFunction public

factorial : Nat → Nat
factorial zero = 1
factorial (suc n) = suc n * factorial n

ratPower : Rational → Nat → Rational
ratPower q zero = rationalNat 1
ratPower q (suc n) = ratMultiply q (ratPower q n)

alternateSign : Nat → Rational → Rational
alternateSign zero q = q
alternateSign (suc n) q = ratNegate (alternateSign n q)

gregoryTerm : Nat → Rational
gregoryTerm n =
  alternateSign n
    (ratDivideByNat
      (rationalNat 1)
      (suc (n + n)))

gregorySum : Nat → Rational
gregorySum zero = rationalNat 0
gregorySum (suc n) =
  ratAdd (gregorySum n) (gregoryTerm n)

piApproximation : Sequence
piApproximation n = ratScale 4 (gregorySum n)

cosineTerm : Rational → Nat → Rational
cosineTerm q n =
  alternateSign n
    (ratDivideByNat
      (ratPower q (n + n))
      (factorial (n + n)))

cosinePartial : Rational → Nat → Rational
cosinePartial q zero = rationalNat 0
cosinePartial q (suc n) =
  ratAdd (cosinePartial q n) (cosineTerm q n)

cosineSequence : Sequence → Sequence
cosineSequence argument n =
  cosinePartial (argument n) (suc n)

rationalPiMultipleSequence : Nat → Nat → Sequence
rationalPiMultipleSequence numerator denominator =
  sequenceDivideByNat
    (sequenceScale numerator piApproximation)
    denominator

cosineOfRationalPiMultiple : Nat → Nat → Sequence
cosineOfRationalPiMultiple numerator denominator =
  cosineSequence
    (rationalPiMultipleSequence numerator denominator)

SpecifiedRoot : Real → Set
SpecifiedRoot x =
  SequenceEquivalent
    (approximation x)
    (cosineOfRationalPiMultiple 2 7)
  ∨
  SequenceEquivalent
    (approximation x)
    (cosineOfRationalPiMultiple 4 7)
  ∨
  SequenceEquivalent
    (approximation x)
    (cosineOfRationalPiMultiple 6 7)

polynomialSequence : Real → Real → Real → Real → Sequence
polynomialSequence a b c x =
  sequenceAdd
    (sequenceAdd
      (sequenceAdd
        (sequencePower (approximation x) 3)
        (sequenceMultiply
          (approximation a)
          (sequencePower (approximation x) 2)))
      (sequenceMultiply
        (approximation b)
        (approximation x)))
    (approximation c)

coefficientProductSequence : Real → Real → Real → Sequence
coefficientProductSequence a b c =
  sequenceMultiply
    (sequenceMultiply
      (approximation a)
      (approximation b))
    (approximation c)

amc12a-2021-p22 : Set
amc12a-2021-p22 =
  (a b c : Real) →
  (f : RealFunction) →
  ((x : Real) →
    SequenceEquivalent
      (approximation (apply f x))
      (polynomialSequence a b c x)) →
  ((x : Real) →
    SequenceEquivalent
      (approximation (apply f x))
      (naturalSequence 0)
    ↔
    SpecifiedRoot x) →
  SequenceEquivalent
    (coefficientProductSequence a b c)
    (ratioSequence 1 32)
