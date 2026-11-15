-- Statement-only formalization of miniF2F artifact aime_1988_p8: a real-valued
-- function on positive natural pairs with diagonal, symmetry, and recurrence
-- conditions, using rational Cauchy sequences for the real numbers. This file
-- contains no proof.

module aime-1988-p8 where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Int using (Int; pos; negsuc)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)

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

data Rational : Set where
  fraction : Int → Nat → Rational

numerator : Rational → Int
numerator (fraction z d) = z

denominator-minus-one : Rational → Nat
denominator-minus-one (fraction z d) = d

denominator : Rational → Nat
denominator q = suc (denominator-minus-one q)

ratZero : Rational
ratZero = fraction (pos zero) zero

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

RealEquivalent : Real → Real → Set
RealEquivalent x y =
  SequenceEquivalent (approximation x) (approximation y)

rationalNat : Nat → Rational
rationalNat n = fraction (pos n) zero

constantSequence : Rational → Sequence
constantSequence q n = q

naturalSequence : Nat → Sequence
naturalSequence n = constantSequence (rationalNat n)

scaleSequence : Nat → Sequence → Sequence
scaleSequence n sequence k =
  ratMultiply (rationalNat n) (sequence k)

RepresentsNat : Real → Nat → Set
RepresentsNat x n =
  SequenceEquivalent
    (approximation x)
    (naturalSequence n)

aime-1988-p8 : Set
aime-1988-p8 =
  (f : Nat → Nat → Real) →
  ((x : Nat) →
    RepresentsNat
      (f (suc x) (suc x))
      (suc x)) →
  ((x y : Nat) →
    RealEquivalent
      (f (suc x) (suc y))
      (f (suc y) (suc x))) →
  ((x y : Nat) →
    SequenceEquivalent
      (scaleSequence
        (suc x + suc y)
        (approximation (f (suc x) (suc y))))
      (scaleSequence
        (suc y)
        (approximation (f (suc x) (suc x + suc y))))) →
  RepresentsNat (f 14 52) 364
