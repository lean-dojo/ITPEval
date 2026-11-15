-- Statement-only formalization of "The Impossibility of Trisecting the Angle and Doubling the
-- Cube" from Hundred Theorems item 008: straightedge-and-compass constructions cannot double
-- the cube or trisect a 60-degree angle. This file contains no proof.

module HundredTheorems008 where

open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)
open import Agda.Builtin.Int using (Int; pos; negsuc)
open import Agda.Builtin.Sigma using (Σ; _,_)

infixr 4 _∧_
infix 3 ¬_

data ⊥ : Set where

data _∧_ (A B : Set) : Set where
  conjunction : A → B → A ∧ B

¬_ : Set → Set
¬ A = A → ⊥

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

natSubtract : Nat → Nat → Nat
natSubtract n zero = n
natSubtract zero (suc m) = zero
natSubtract (suc n) (suc m) = natSubtract n m

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

intSubtract : Int → Int → Int
intSubtract a b = intAdd a (intNegate b)

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

ratZero : Rational
ratZero = fraction (pos zero) zero

ratOne : Rational
ratOne = fraction (pos (suc zero)) zero

ratTwo : Rational
ratTwo = fraction (pos (suc (suc zero))) zero

ratFour : Rational
ratFour = fraction (pos (suc (suc (suc (suc zero))))) zero

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

realNegate : Real → Real
realNegate x n = ratNegate (x n)

realAdd : Real → Real → Real
realAdd x y n = ratAdd (x n) (y n)

realSubtract : Real → Real → Real
realSubtract x y n = ratSubtract (x n) (y n)

realMultiply : Real → Real → Real
realMultiply x y n = ratMultiply (x n) (y n)

realSquare : Real → Real
realSquare x = realMultiply x x

realCube : Real → Real
realCube x = realMultiply (realSquare x) x

realScaleNat : Nat → Real → Real
realScaleNat coefficient x n =
  ratMultiply (rationalFromNat coefficient) (x n)

RealEquivalent : Real → Real → Set
RealEquivalent = SequenceEquivalent

RationalReal : Real → Set
RationalReal x =
  Exists Rational
    (λ q → RealEquivalent x (constantSequence q))

record Point : Set where
  constructor point
  field
    x-coordinate : Real
    y-coordinate : Real

open Point

ValidPoint : Point → Set
ValidPoint p = Cauchy (x-coordinate p) ∧ Cauchy (y-coordinate p)

PointEquivalent : Point → Point → Set
PointEquivalent p q =
  RealEquivalent (x-coordinate p) (x-coordinate q) ∧
  RealEquivalent (y-coordinate p) (y-coordinate q)

Parallel : Point → Point → Point → Point → Set
Parallel a b c d =
  RealEquivalent
    (realMultiply
      (realSubtract (x-coordinate a) (x-coordinate b))
      (realSubtract (y-coordinate c) (y-coordinate d)))
    (realMultiply
      (realSubtract (y-coordinate a) (y-coordinate b))
      (realSubtract (x-coordinate c) (x-coordinate d)))

Collinear : Point → Point → Point → Set
Collinear a b c =
  RealEquivalent
    (realMultiply
      (realSubtract (x-coordinate a) (x-coordinate b))
      (realSubtract (y-coordinate b) (y-coordinate c)))
    (realMultiply
      (realSubtract (y-coordinate a) (y-coordinate b))
      (realSubtract (x-coordinate b) (x-coordinate c)))

SquaredDistance : Point → Point → Real
SquaredDistance p q =
  realAdd
    (realSquare
      (realSubtract (x-coordinate p) (x-coordinate q)))
    (realSquare
      (realSubtract (y-coordinate p) (y-coordinate q)))

EqualSquaredDistance : Point → Point → Point → Point → Set
EqualSquaredDistance a b c d =
  RealEquivalent (SquaredDistance a b) (SquaredDistance c d)

IsIntersection :
  Point →
  Point →
  Point →
  Point →
  Point →
  Set
IsIntersection a b c d m =
  Collinear a b m ∧ Collinear c d m

data Constructible : Point → Set where
  rational-point :
    {p : Point} →
    ValidPoint p →
    RationalReal (x-coordinate p) →
    RationalReal (y-coordinate p) →
    Constructible p

  line-line-intersection :
    {a b c d m : Point} →
    Constructible a →
    Constructible b →
    Constructible c →
    Constructible d →
    ¬ Parallel a b c d →
    IsIntersection a b c d m →
    ValidPoint m →
    Constructible m

  line-circle-intersection :
    {a b c d e m : Point} →
    Constructible a →
    Constructible b →
    Constructible c →
    Constructible d →
    Constructible e →
    ¬ PointEquivalent a b →
    Collinear a b m →
    EqualSquaredDistance c m d e →
    ValidPoint m →
    Constructible m

  circle-circle-intersection :
    {a b c d e f m : Point} →
    Constructible a →
    Constructible b →
    Constructible c →
    Constructible d →
    Constructible e →
    Constructible f →
    ¬ (PointEquivalent a d ∧ EqualSquaredDistance b c e f) →
    EqualSquaredDistance a m b c →
    EqualSquaredDistance d m e f →
    ValidPoint m →
    Constructible m

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

NinthOfPi : Real → Real → Set
NinthOfPi angle pi =
  RealEquivalent (realScaleNat (suc (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))) angle) pi

CubeEqualsTwo : Real → Set
CubeEqualsTwo x =
  RealEquivalent (realCube x) (constantSequence ratTwo)

DoublingTheCube : Set
DoublingTheCube =
  (x : Real) →
  Cauchy x →
  CubeEqualsTwo x →
  ¬ Constructible (point x (constantSequence ratZero))

TrisectingSixtyDegrees : Set
TrisectingSixtyDegrees =
  (pi angle cosine-value y : Real) →
  Cauchy pi →
  Pi pi →
  Cauchy angle →
  NinthOfPi angle pi →
  Cauchy cosine-value →
  CosineAt angle cosine-value →
  Cauchy y →
  ¬ Constructible (point cosine-value y)

hundred-theorems-008 : Set
hundred-theorems-008 =
  DoublingTheCube ∧ TrisectingSixtyDegrees
