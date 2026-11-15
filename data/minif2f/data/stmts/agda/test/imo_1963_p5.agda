-- Statement-only formalization of miniF2F test problem imo_1963_p5: the cosine
-- identity cos(pi/7) - cos(2*pi/7) + cos(3*pi/7) = 1/2 over the real numbers.
-- This file contains no proof.

{-# OPTIONS --safe #-}

module imo-1963-p5 where

open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)
open import Agda.Builtin.Int using (Int; pos; negsuc)
open import Agda.Builtin.Sigma using (Σ)

Exists : (A : Set) → (A → Set) → Set
Exists A P = Σ A P

data NatLessOrEqual : Nat → Nat → Set where
  zero-less-or-equal : {n : Nat} → NatLessOrEqual zero n
  suc-less-or-equal :
    {m n : Nat} →
    NatLessOrEqual m n →
    NatLessOrEqual (suc m) (suc n)

natPred : Nat → Nat
natPred zero = zero
natPred (suc n) = n

negative : Nat → Int
negative zero = pos zero
negative (suc n) = negsuc n

intNegate : Int → Int
intNegate (pos n) = negative n
intNegate (negsuc n) = pos (suc n)

intDifference : Nat → Nat → Int
intDifference zero zero = pos zero
intDifference (suc m) zero = pos (suc m)
intDifference zero (suc n) = negsuc n
intDifference (suc m) (suc n) = intDifference m n

intAdd : Int → Int → Int
intAdd (pos m) (pos n) = pos (m + n)
intAdd (pos m) (negsuc n) = intDifference m (suc n)
intAdd (negsuc m) (pos n) = intDifference n (suc m)
intAdd (negsuc m) (negsuc n) = negsuc (suc (m + n))

intMultiply : Int → Int → Int
intMultiply (pos m) (pos n) = pos (m * n)
intMultiply (pos m) (negsuc n) = negative (m * suc n)
intMultiply (negsuc m) (pos n) = negative (suc m * n)
intMultiply (negsuc m) (negsuc n) = pos (suc m * suc n)

scaleInt : Int → Nat → Int
scaleInt z n = intMultiply z (pos n)

intAbs : Int → Nat
intAbs (pos n) = n
intAbs (negsuc n) = suc n

record Rational : Set where
  constructor fraction
  field
    numerator : Int
    denominator-minus-one : Nat

open Rational

denominator : Rational → Nat
denominator q = suc (denominator-minus-one q)

ratOne : Rational
ratOne = fraction (pos (suc zero)) zero

ratFour : Rational
ratFour = fraction (pos 4) zero

ratHalf : Rational
ratHalf = fraction (pos (suc zero)) (suc zero)

rationalFromNat : Nat → Rational
rationalFromNat n = fraction (pos n) zero

ratNegate : Rational → Rational
ratNegate q =
  fraction
    (intNegate (numerator q))
    (denominator-minus-one q)

ratAdd : Rational → Rational → Rational
ratAdd p q =
  fraction
    (intAdd
      (intMultiply (numerator p) (pos (denominator q)))
      (intMultiply (numerator q) (pos (denominator p))))
    (natPred (denominator p * denominator q))

ratSubtract : Rational → Rational → Rational
ratSubtract p q = ratAdd p (ratNegate q)

ratMultiply : Rational → Rational → Rational
ratMultiply p q =
  fraction
    (intMultiply (numerator p) (numerator q))
    (natPred (denominator p * denominator q))

ratPower : Rational → Nat → Rational
ratPower q zero = ratOne
ratPower q (suc n) = ratMultiply q (ratPower q n)

data IntLessOrEqual : Int → Int → Set where
  positive-less-or-equal-positive :
    {m n : Nat} →
    NatLessOrEqual m n →
    IntLessOrEqual (pos m) (pos n)
  negative-less-or-equal-positive :
    {m n : Nat} →
    IntLessOrEqual (negsuc m) (pos n)
  negative-less-or-equal-negative :
    {m n : Nat} →
    NatLessOrEqual n m →
    IntLessOrEqual (negsuc m) (negsuc n)

ratLessOrEqual : Rational → Rational → Set
ratLessOrEqual p q =
  IntLessOrEqual
    (scaleInt (numerator p) (denominator q))
    (scaleInt (numerator q) (denominator p))

ratAbsolute : Rational → Rational
ratAbsolute q =
  fraction
    (pos (intAbs (numerator q)))
    (denominator-minus-one q)

ratAbsDifference : Rational → Rational → Rational
ratAbsDifference p q = ratAbsolute (ratSubtract p q)

unitFraction : Nat → Rational
unitFraction precision = fraction (pos (suc zero)) precision

Sequence : Set
Sequence = Nat → Rational

Cauchy : Sequence → Set
Cauchy sequence =
  (precision : Nat) →
  Exists Nat
    (λ threshold →
      (m n : Nat) →
      NatLessOrEqual threshold m →
      NatLessOrEqual threshold n →
      ratLessOrEqual
        (ratAbsDifference (sequence m) (sequence n))
        (unitFraction precision))

SequenceEquivalent : Sequence → Sequence → Set
SequenceEquivalent left right =
  (precision : Nat) →
  Exists Nat
    (λ threshold →
      (n : Nat) →
      NatLessOrEqual threshold n →
      ratLessOrEqual
        (ratAbsDifference (left n) (right n))
        (unitFraction precision))

Real : Set
Real = Sequence

constantSequence : Rational → Real
constantSequence q n = q

realAdd : Real → Real → Real
realAdd x y n = ratAdd (x n) (y n)

realSubtract : Real → Real → Real
realSubtract x y n = ratSubtract (x n) (y n)

realScaleNat : Nat → Real → Real
realScaleNat coefficient x n =
  ratMultiply (rationalFromNat coefficient) (x n)

RealEquivalent : Real → Real → Set
RealEquivalent = SequenceEquivalent

alternatingSign : Nat → Int
alternatingSign zero = pos (suc zero)
alternatingSign (suc n) = intNegate (alternatingSign n)

oddNatural : Nat → Nat
oddNatural n = suc (n + n)

leibnizTerm : Nat → Rational
leibnizTerm n =
  fraction
    (alternatingSign n)
    (natPred (oddNatural n))

leibnizPartialSum : Nat → Rational
leibnizPartialSum zero = leibnizTerm zero
leibnizPartialSum (suc n) =
  ratAdd (leibnizPartialSum n) (leibnizTerm (suc n))

piApproximation : Real
piApproximation n =
  ratMultiply ratFour (leibnizPartialSum n)

Pi : Real → Set
Pi value = RealEquivalent value piApproximation

factorial : Nat → Nat
factorial zero = suc zero
factorial (suc n) = suc n * factorial n

twice : Nat → Nat
twice n = n + n

ratDivideByFactorial : Rational → Nat → Rational
ratDivideByFactorial q n =
  fraction
    (numerator q)
    (natPred (denominator q * factorial n))

cosineSign : Nat → Rational
cosineSign n = fraction (alternatingSign n) zero

cosineTerm : Rational → Nat → Rational
cosineTerm x n =
  ratDivideByFactorial
    (ratMultiply
      (cosineSign n)
      (ratPower x (twice n)))
    (twice n)

cosinePartialSum : Rational → Nat → Rational
cosinePartialSum x zero = cosineTerm x zero
cosinePartialSum x (suc n) =
  ratAdd
    (cosinePartialSum x n)
    (cosineTerm x (suc n))

cosineApproximation : Real → Real
cosineApproximation angle n =
  cosinePartialSum (angle n) n

CosineAt : Real → Real → Set
CosineAt angle value =
  RealEquivalent value (cosineApproximation angle)

SeventhOfPi : Real → Real → Set
SeventhOfPi angle pi =
  RealEquivalent (realScaleNat 7 angle) pi

imo-1963-p5 : Set
imo-1963-p5 =
  (pi angle cosine-one cosine-two cosine-three : Real) →
  Cauchy pi →
  Pi pi →
  Cauchy angle →
  SeventhOfPi angle pi →
  Cauchy cosine-one →
  CosineAt angle cosine-one →
  Cauchy cosine-two →
  CosineAt (realScaleNat 2 angle) cosine-two →
  Cauchy cosine-three →
  CosineAt (realScaleNat 3 angle) cosine-three →
  RealEquivalent
    (realAdd
      (realSubtract cosine-one cosine-two)
      cosine-three)
    (constantSequence ratHalf)
