-- Statement-only formalization of "Green's Theorem" from Hundred Theorems item 021:
-- over Cauchy-sequence real numbers, a closed absolutely continuous plane curve
-- having winding number one on its inside (the bounded complement components)
-- equates the
-- boundary line integral of a differentiable vector field with its curl integral.
-- This file contains no proof.

open import Agda.Builtin.Equality renaming (_≡_ to _==_)
open import Agda.Builtin.Int using (Int; pos; negsuc)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)

infix 4 _!=_ _<=N_ _<N_

data Bottom : Set where

Not : Set -> Set
Not A = A -> Bottom

_!=_ : {A : Set} -> A -> A -> Set
x != y = Not (x == y)

record Both (A B : Set) : Set where
  constructor both
  field
    first  : A
    second : B

data Either (A B : Set) : Set where
  left  : A -> Either A B
  right : B -> Either A B

record Equivalent (A B : Set) : Set where
  constructor equivalent
  field
    forward  : A -> B
    backward : B -> A

record Exists (A : Set) (P : A -> Set) : Set where
  constructor witness
  field
    value    : A
    property : P value

data _<=N_ : Nat -> Nat -> Set where
  zero<= : {n : Nat} -> zero <=N n
  suc<=suc : {m n : Nat} -> m <=N n -> suc m <=N suc n

_<N_ : Nat -> Nat -> Set
m <N n = suc m <=N n

pred : Nat -> Nat
pred zero = zero
pred (suc n) = n

negative : Nat -> Int
negative zero = pos zero
negative (suc n) = negsuc n

negateInt : Int -> Int
negateInt (pos n) = negative n
negateInt (negsuc n) = pos (suc n)

difference : Nat -> Nat -> Int
difference zero zero = pos zero
difference (suc m) zero = pos (suc m)
difference zero (suc n) = negsuc n
difference (suc m) (suc n) = difference m n

addInt : Int -> Int -> Int
addInt (pos m) (pos n) = pos (m + n)
addInt (pos m) (negsuc n) = difference m (suc n)
addInt (negsuc m) (pos n) = difference n (suc m)
addInt (negsuc m) (negsuc n) = negsuc (suc (m + n))

multiplyInt : Int -> Int -> Int
multiplyInt (pos m) (pos n) = pos (m * n)
multiplyInt (pos m) (negsuc n) = negative (m * suc n)
multiplyInt (negsuc m) (pos n) = negative (suc m * n)
multiplyInt (negsuc m) (negsuc n) = pos (suc m * suc n)

scaleInt : Int -> Nat -> Int
scaleInt z n = multiplyInt z (pos n)

absoluteInt : Int -> Nat
absoluteInt (pos n) = n
absoluteInt (negsuc n) = suc n

data IntLessOrEqual : Int -> Int -> Set where
  positive<=positive :
    {m n : Nat} ->
    m <=N n ->
    IntLessOrEqual (pos m) (pos n)
  negative<=positive :
    {m n : Nat} ->
    IntLessOrEqual (negsuc m) (pos n)
  negative<=negative :
    {m n : Nat} ->
    n <=N m ->
    IntLessOrEqual (negsuc m) (negsuc n)

record Rational : Set where
  constructor fraction
  field
    numerator             : Int
    denominator-minus-one : Nat

open Rational public

denominator : Rational -> Nat
denominator q = suc (denominator-minus-one q)

ratZero : Rational
ratZero = fraction (pos zero) zero

ratOne : Rational
ratOne = fraction (pos (suc zero)) zero

ratFour : Rational
ratFour = fraction (pos (suc (suc (suc (suc zero))))) zero

unitFraction : Nat -> Rational
unitFraction n = fraction (pos (suc zero)) n

ratNegate : Rational -> Rational
ratNegate q =
  fraction (negateInt (numerator q)) (denominator-minus-one q)

ratAdd : Rational -> Rational -> Rational
ratAdd x y =
  fraction
    (addInt
      (scaleInt (numerator x) (denominator y))
      (scaleInt (numerator y) (denominator x)))
    (pred (denominator x * denominator y))

ratSubtract : Rational -> Rational -> Rational
ratSubtract x y = ratAdd x (ratNegate y)

ratMultiply : Rational -> Rational -> Rational
ratMultiply x y =
  fraction
    (multiplyInt (numerator x) (numerator y))
    (pred (denominator x * denominator y))

ratAbsolute : Rational -> Rational
ratAbsolute q =
  fraction
    (pos (absoluteInt (numerator q)))
    (denominator-minus-one q)

RationalEquivalent : Rational -> Rational -> Set
RationalEquivalent x y =
  scaleInt (numerator x) (denominator y) ==
  scaleInt (numerator y) (denominator x)

RationalLessOrEqual : Rational -> Rational -> Set
RationalLessOrEqual x y =
  IntLessOrEqual
    (scaleInt (numerator x) (denominator y))
    (scaleInt (numerator y) (denominator x))

RationalDistanceWithin : Rational -> Rational -> Rational -> Set
RationalDistanceWithin x y epsilon =
  RationalLessOrEqual
    (ratAbsolute (ratSubtract x y))
    epsilon

Sequence : Set
Sequence = Nat -> Rational

Cauchy : Sequence -> Set
Cauchy sequence =
  (precision : Nat) ->
  Exists Nat
    (\ cutoff ->
      (m n : Nat) ->
      cutoff <=N m ->
      cutoff <=N n ->
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

SequenceEquivalent : Sequence -> Sequence -> Set
SequenceEquivalent leftSequence rightSequence =
  (precision : Nat) ->
  Exists Nat
    (\ cutoff ->
      (n : Nat) ->
      cutoff <=N n ->
      RationalDistanceWithin
        (leftSequence n)
        (rightSequence n)
        (unitFraction precision))

SequenceLessOrEqual : Sequence -> Sequence -> Set
SequenceLessOrEqual leftSequence rightSequence =
  (precision : Nat) ->
  Exists Nat
    (\ cutoff ->
      (n : Nat) ->
      cutoff <=N n ->
      RationalLessOrEqual
        (leftSequence n)
        (ratAdd (rightSequence n) (unitFraction precision)))

SequenceStrictLess : Sequence -> Sequence -> Set
SequenceStrictLess leftSequence rightSequence =
  Exists Nat
    (\ margin ->
      Exists Nat
        (\ cutoff ->
          (n : Nat) ->
          cutoff <=N n ->
          RationalLessOrEqual
            (ratAdd (leftSequence n) (unitFraction margin))
            (rightSequence n)))

RealEquivalent : Real -> Real -> Set
RealEquivalent x y =
  SequenceEquivalent (approximation x) (approximation y)

RealLessOrEqual : Real -> Real -> Set
RealLessOrEqual x y =
  SequenceLessOrEqual (approximation x) (approximation y)

RealStrictLess : Real -> Real -> Set
RealStrictLess x y =
  SequenceStrictLess (approximation x) (approximation y)

constantSequence : Rational -> Sequence
constantSequence q n = q

Nonnegative : Real -> Set
Nonnegative x =
  SequenceLessOrEqual
    (constantSequence ratZero)
    (approximation x)

Positive : Real -> Set
Positive x =
  SequenceStrictLess
    (constantSequence ratZero)
    (approximation x)

alternatingSign : Nat -> Int
alternatingSign zero = pos (suc zero)
alternatingSign (suc n) = negateInt (alternatingSign n)

oddNatural : Nat -> Nat
oddNatural n = suc (n + n)

leibnizTerm : Nat -> Rational
leibnizTerm n =
  fraction
    (alternatingSign n)
    (pred (oddNatural n))

leibnizPartialSum : Nat -> Rational
leibnizPartialSum zero = leibnizTerm zero
leibnizPartialSum (suc n) =
  ratAdd (leibnizPartialSum n) (leibnizTerm (suc n))

piSequence : Sequence
piSequence n =
  ratMultiply ratFour (leibnizPartialSum n)

record ConcreteRealOperations : Set1 where
  field
    zeroR oneR piR : Real
    addR multiplyR : Real -> Real -> Real
    negateR inverseR squareRootR : Real -> Real

    zero-semantics :
      SequenceEquivalent
        (approximation zeroR)
        (constantSequence ratZero)
    one-semantics :
      SequenceEquivalent
        (approximation oneR)
        (constantSequence ratOne)
    pi-semantics :
      SequenceEquivalent
        (approximation piR)
        piSequence
    add-semantics :
      (x y : Real) ->
      SequenceEquivalent
        (approximation (addR x y))
        (\ n -> ratAdd (approximation x n) (approximation y n))
    multiply-semantics :
      (x y : Real) ->
      SequenceEquivalent
        (approximation (multiplyR x y))
        (\ n -> ratMultiply (approximation x n) (approximation y n))
    negate-semantics :
      (x : Real) ->
      SequenceEquivalent
        (approximation (negateR x))
        (\ n -> ratNegate (approximation x n))
    inverse-zero-semantics :
      RealEquivalent (inverseR zeroR) zeroR
    inverse-semantics :
      (x : Real) ->
      Not (RealEquivalent x zeroR) ->
      RealEquivalent (multiplyR x (inverseR x)) oneR
    square-root-nonnegative :
      (x : Real) -> Nonnegative (squareRootR x)
    square-root-semantics :
      (x : Real) ->
      Nonnegative x ->
      RealEquivalent
        (multiplyR (squareRootR x) (squareRootR x))
        x

    add-respects-equivalence :
      (a b c d : Real) ->
      RealEquivalent a b ->
      RealEquivalent c d ->
      RealEquivalent (addR a c) (addR b d)
    multiply-respects-equivalence :
      (a b c d : Real) ->
      RealEquivalent a b ->
      RealEquivalent c d ->
      RealEquivalent (multiplyR a c) (multiplyR b d)
    negate-respects-equivalence :
      (a b : Real) ->
      RealEquivalent a b ->
      RealEquivalent (negateR a) (negateR b)
    inverse-respects-equivalence :
      (a b : Real) ->
      RealEquivalent a b ->
      RealEquivalent (inverseR a) (inverseR b)
    square-root-respects-equivalence :
      (a b : Real) ->
      RealEquivalent a b ->
      RealEquivalent (squareRootR a) (squareRootR b)

open ConcreteRealOperations

subtractR : ConcreteRealOperations -> Real -> Real -> Real
subtractR operations x y =
  addR operations x (negateR operations y)

divideR : ConcreteRealOperations -> Real -> Real -> Real
divideR operations x y =
  multiplyR operations x (inverseR operations y)

twoPi : ConcreteRealOperations -> Real
twoPi operations =
  addR operations (piR operations) (piR operations)

realSquare : ConcreteRealOperations -> Real -> Real
realSquare operations x =
  multiplyR operations x x

realDistance : ConcreteRealOperations -> Real -> Real -> Real
realDistance operations x y =
  squareRootR operations
    (realSquare operations (subtractR operations x y))

record Point : Set where
  constructor point
  field
    x-coordinate : Real
    y-coordinate : Real

open Point public

PointEquivalent : Point -> Point -> Set
PointEquivalent p q =
  Both
    (RealEquivalent (x-coordinate p) (x-coordinate q))
    (RealEquivalent (y-coordinate p) (y-coordinate q))

zeroPoint : ConcreteRealOperations -> Point
zeroPoint operations =
  point (zeroR operations) (zeroR operations)

addPoint : ConcreteRealOperations -> Point -> Point -> Point
addPoint operations p q =
  point
    (addR operations (x-coordinate p) (x-coordinate q))
    (addR operations (y-coordinate p) (y-coordinate q))

subtractPoint : ConcreteRealOperations -> Point -> Point -> Point
subtractPoint operations p q =
  point
    (subtractR operations (x-coordinate p) (x-coordinate q))
    (subtractR operations (y-coordinate p) (y-coordinate q))

scalePoint : ConcreteRealOperations -> Real -> Point -> Point
scalePoint operations scalar p =
  point
    (multiplyR operations scalar (x-coordinate p))
    (multiplyR operations scalar (y-coordinate p))

pointDistanceSquared :
  ConcreteRealOperations ->
  Point ->
  Point ->
  Real
pointDistanceSquared operations p q =
  addR operations
    (realSquare operations
      (subtractR operations (x-coordinate p) (x-coordinate q)))
    (realSquare operations
      (subtractR operations (y-coordinate p) (y-coordinate q)))

pointDistance :
  ConcreteRealOperations ->
  Point ->
  Point ->
  Real
pointDistance operations p q =
  squareRootR operations (pointDistanceSquared operations p q)

PointClose :
  ConcreteRealOperations ->
  Point ->
  Point ->
  Real ->
  Set
PointClose operations p q epsilon =
  RealStrictLess (pointDistance operations p q) epsilon

Region : Set1
Region = Point -> Set

RegionExtensional : Region -> Set
RegionExtensional region =
  (p q : Point) ->
  PointEquivalent p q ->
  Equivalent (region p) (region q)

Subset : Region -> Region -> Set
Subset smaller larger =
  (p : Point) -> smaller p -> larger p

Union : Region -> Region -> Region
Union leftRegion rightRegion p =
  Either (leftRegion p) (rightRegion p)

Complement : Region -> Region
Complement region p =
  Not (region p)

ClosedInterval :
  Real ->
  Real ->
  Real ->
  Set
ClosedInterval a b t =
  Both (RealLessOrEqual a t) (RealLessOrEqual t b)

UnitInterval : ConcreteRealOperations -> Real -> Set
UnitInterval operations =
  ClosedInterval (zeroR operations) (oneR operations)

record Curve : Set where
  constructor curve
  field
    curveValue : Real -> Point
    curve-extensional :
      (s t : Real) ->
      RealEquivalent s t ->
      PointEquivalent (curveValue s) (curveValue t)

open Curve public

record VectorField : Set where
  constructor vectorField
  field
    fieldValue : Point -> Point
    field-extensional :
      (p q : Point) ->
      PointEquivalent p q ->
      PointEquivalent (fieldValue p) (fieldValue q)

open VectorField public

pathImage :
  ConcreteRealOperations ->
  Curve ->
  Region
pathImage operations g p =
  Exists Real
    (\ t ->
      Both
        (UnitInterval operations t)
        (PointEquivalent (curveValue g t) p))

OpenRegion :
  ConcreteRealOperations ->
  Region ->
  Set
OpenRegion operations region =
  Both
    (RegionExtensional region)
    ((p : Point) ->
      region p ->
      Exists Real
        (\ radius ->
          Both
            (Positive radius)
            ((q : Point) ->
              PointClose operations p q radius ->
              region q)))

ContinuousCurveOnUnit :
  ConcreteRealOperations ->
  Curve ->
  Set
ContinuousCurveOnUnit operations g =
  (t : Real) ->
  UnitInterval operations t ->
  (epsilon : Real) ->
  Positive epsilon ->
  Exists Real
    (\ delta ->
      Both
        (Positive delta)
        ((s : Real) ->
          UnitInterval operations s ->
          RealStrictLess (realDistance operations s t) delta ->
          PointClose
            operations
            (curveValue g s)
            (curveValue g t)
            epsilon))

SameComplementComponent :
  ConcreteRealOperations ->
  Region ->
  Point ->
  Point ->
  Set
SameComplementComponent operations boundary p q =
  Exists Curve
    (\ connector ->
      Both
        (PointEquivalent
          (curveValue connector (zeroR operations))
          p)
        (Both
          (PointEquivalent
            (curveValue connector (oneR operations))
            q)
          (Both
            (ContinuousCurveOnUnit operations connector)
            ((t : Real) ->
              UnitInterval operations t ->
              Not (boundary (curveValue connector t))))))

Inside :
  ConcreteRealOperations ->
  Region ->
  Region
Inside operations boundary p =
  Both
    (Not (boundary p))
    (Exists Point
      (\ center ->
        Exists Real
          (\ radius ->
            Both
              (Positive radius)
              ((q : Point) ->
                SameComplementComponent operations boundary p q ->
                RealLessOrEqual
                  (pointDistance operations q center)
                  radius))))

record Matrix : Set where
  constructor matrix
  field
    entry11 : Real
    entry12 : Real
    entry21 : Real
    entry22 : Real

open Matrix public

applyMatrix :
  ConcreteRealOperations ->
  Matrix ->
  Point ->
  Point
applyMatrix operations derivative h =
  point
    (addR operations
      (multiplyR operations (entry11 derivative) (x-coordinate h))
      (multiplyR operations (entry12 derivative) (y-coordinate h)))
    (addR operations
      (multiplyR operations (entry21 derivative) (x-coordinate h))
      (multiplyR operations (entry22 derivative) (y-coordinate h)))

HasFrechetDerivativeAt :
  ConcreteRealOperations ->
  VectorField ->
  Point ->
  Matrix ->
  Set
HasFrechetDerivativeAt operations f z derivative =
  (epsilon : Real) ->
  Positive epsilon ->
  Exists Real
    (\ delta ->
      Both
        (Positive delta)
        ((w : Point) ->
          PointClose operations w z delta ->
          RealLessOrEqual
            (pointDistanceSquared operations
              (subtractPoint operations
                (subtractPoint operations
                  (fieldValue f w)
                  (fieldValue f z))
                (applyMatrix operations derivative
                  (subtractPoint operations w z)))
              (zeroPoint operations))
            (multiplyR operations
              (realSquare operations epsilon)
              (pointDistanceSquared operations w z))))

HasVectorDerivativeAt :
  ConcreteRealOperations ->
  Curve ->
  Real ->
  Point ->
  Set
HasVectorDerivativeAt operations g t derivative =
  (epsilon : Real) ->
  Positive epsilon ->
  Exists Real
    (\ delta ->
      Both
        (Positive delta)
        ((s : Real) ->
          RealStrictLess (realDistance operations s t) delta ->
          RealLessOrEqual
            (pointDistanceSquared operations
              (subtractPoint operations
                (subtractPoint operations
                  (curveValue g s)
                  (curveValue g t))
                (scalePoint operations
                  (subtractR operations s t)
                  derivative))
              (zeroPoint operations))
            (multiplyR operations
              (realSquare operations epsilon)
              (realSquare operations
                (subtractR operations s t)))))

DifferentiableOn :
  ConcreteRealOperations ->
  VectorField ->
  Region ->
  Set
DifferentiableOn operations f region =
  (z : Point) ->
  region z ->
  Exists Matrix (HasFrechetDerivativeAt operations f z)

ContinuousVectorOn :
  ConcreteRealOperations ->
  (Point -> Point) ->
  Region ->
  Set
ContinuousVectorOn operations function region =
  (z : Point) ->
  region z ->
  (epsilon : Real) ->
  Positive epsilon ->
  Exists Real
    (\ delta ->
      Both
        (Positive delta)
        ((w : Point) ->
          region w ->
          PointClose operations w z delta ->
          PointClose operations (function w) (function z) epsilon))

record DerivativeSelections
  (operations : ConcreteRealOperations) : Set1 where
  field
    frechetDerivative :
      VectorField ->
      Point ->
      Matrix
    frechet-derivative-correct :
      (f : VectorField) ->
      (z : Point) ->
      Exists Matrix (HasFrechetDerivativeAt operations f z) ->
      HasFrechetDerivativeAt operations f z
        (frechetDerivative f z)

    vectorDerivative :
      Curve ->
      Real ->
      Point
    vector-derivative-correct :
      (g : Curve) ->
      (t : Real) ->
      Exists Point (HasVectorDerivativeAt operations g t) ->
      HasVectorDerivativeAt operations g t
        (vectorDerivative g t)
    vector-derivative-zero-otherwise :
      (g : Curve) ->
      (t : Real) ->
      Not (Exists Point (HasVectorDerivativeAt operations g t)) ->
      PointEquivalent
        (vectorDerivative g t)
        (zeroPoint operations)

open DerivativeSelections

record IntervalFamily : Set where
  constructor intervalFamily
  field
    interval-count : Nat
    interval-left  : Nat -> Real
    interval-right : Nat -> Real

open IntervalFamily public

FamilyInsideUnit :
  ConcreteRealOperations ->
  IntervalFamily ->
  Set
FamilyInsideUnit operations family =
  Both
    ((i : Nat) ->
      i <N interval-count family ->
      Both
        (UnitInterval operations (interval-left family i))
        (UnitInterval operations (interval-right family i)))
    (Both
      ((i : Nat) ->
        i <N interval-count family ->
        RealLessOrEqual
          (interval-left family i)
          (interval-right family i))
      ((i j : Nat) ->
        i <N interval-count family ->
        j <N interval-count family ->
        i != j ->
        Either
          (RealLessOrEqual
            (interval-right family i)
            (interval-left family j))
          (RealLessOrEqual
            (interval-right family j)
            (interval-left family i))))

sumReals :
  ConcreteRealOperations ->
  (Nat -> Real) ->
  Nat ->
  Real
sumReals operations term zero =
  zeroR operations
sumReals operations term (suc n) =
  addR operations
    (sumReals operations term n)
    (term n)

familyTotalLength :
  ConcreteRealOperations ->
  IntervalFamily ->
  Real
familyTotalLength operations family =
  sumReals operations
    (\ i ->
      subtractR operations
        (interval-right family i)
        (interval-left family i))
    (interval-count family)

familyTotalVariation :
  ConcreteRealOperations ->
  Curve ->
  IntervalFamily ->
  Real
familyTotalVariation operations g family =
  sumReals operations
    (\ i ->
      pointDistance operations
        (curveValue g (interval-right family i))
        (curveValue g (interval-left family i)))
    (interval-count family)

AbsolutelyContinuousOnUnit :
  ConcreteRealOperations ->
  Curve ->
  Set
AbsolutelyContinuousOnUnit operations g =
  (epsilon : Real) ->
  Positive epsilon ->
  Exists Real
    (\ delta ->
      Both
        (Positive delta)
        ((family : IntervalFamily) ->
          FamilyInsideUnit operations family ->
          RealStrictLess
            (familyTotalLength operations family)
            delta ->
          RealStrictLess
            (familyTotalVariation operations g family)
            epsilon))

record TaggedDivision : Set where
  constructor taggedDivision
  field
    division-count : Nat
    division-point : Nat -> Real
    division-tag   : Nat -> Real

open TaggedDivision public

TaggedDivisionOf :
  Real ->
  Real ->
  TaggedDivision ->
  Set
TaggedDivisionOf a b division =
  Both
    (RealEquivalent (division-point division zero) a)
    (Both
      (RealEquivalent
        (division-point division (division-count division))
        b)
      (Both
        ((i : Nat) ->
          i <N division-count division ->
          RealLessOrEqual
            (division-point division i)
            (division-point division (suc i)))
        ((i : Nat) ->
          i <N division-count division ->
          ClosedInterval
            (division-point division i)
            (division-point division (suc i))
            (division-tag division i))))

Gauge1 : Set
Gauge1 = Real -> Real

PositiveGauge1 :
  Gauge1 ->
  Set
PositiveGauge1 gauge =
  (t : Real) -> Positive (gauge t)

GaugeFine1 :
  ConcreteRealOperations ->
  Gauge1 ->
  TaggedDivision ->
  Set
GaugeFine1 operations gauge division =
  (i : Nat) ->
  i <N division-count division ->
  (x : Real) ->
  ClosedInterval
    (division-point division i)
    (division-point division (suc i))
    x ->
  RealStrictLess
    (realDistance operations x (division-tag division i))
    (gauge (division-tag division i))

riemannSum1 :
  ConcreteRealOperations ->
  (Real -> Real) ->
  TaggedDivision ->
  Real
riemannSum1 operations integrand division =
  sumReals operations
    (\ i ->
      multiplyR operations
        (integrand (division-tag division i))
        (subtractR operations
          (division-point division (suc i))
          (division-point division i)))
    (division-count division)

HasIntervalIntegral :
  ConcreteRealOperations ->
  (Real -> Real) ->
  Real ->
  Real ->
  Real ->
  Set
HasIntervalIntegral operations integrand a b integral =
  (epsilon : Real) ->
  Positive epsilon ->
  Exists Gauge1
    (\ gauge ->
      Both
        (PositiveGauge1 gauge)
        ((division : TaggedDivision) ->
          TaggedDivisionOf a b division ->
          GaugeFine1 operations gauge division ->
          RealStrictLess
            (realDistance operations
              (riemannSum1 operations integrand division)
              integral)
            epsilon))

record Box : Set where
  constructor box
  field
    lower-left  : Point
    upper-right : Point

open Box public

ValidBox : Box -> Set
ValidBox rectangle =
  Both
    (RealLessOrEqual
      (x-coordinate (lower-left rectangle))
      (x-coordinate (upper-right rectangle)))
    (RealLessOrEqual
      (y-coordinate (lower-left rectangle))
      (y-coordinate (upper-right rectangle)))

PointInBox : Box -> Point -> Set
PointInBox rectangle p =
  Both
    (ClosedInterval
      (x-coordinate (lower-left rectangle))
      (x-coordinate (upper-right rectangle))
      (x-coordinate p))
    (ClosedInterval
      (y-coordinate (lower-left rectangle))
      (y-coordinate (upper-right rectangle))
      (y-coordinate p))

PointInBoxInterior : Box -> Point -> Set
PointInBoxInterior rectangle p =
  Both
    (Both
      (RealStrictLess
        (x-coordinate (lower-left rectangle))
        (x-coordinate p))
      (RealStrictLess
        (x-coordinate p)
        (x-coordinate (upper-right rectangle))))
    (Both
      (RealStrictLess
        (y-coordinate (lower-left rectangle))
        (y-coordinate p))
      (RealStrictLess
        (y-coordinate p)
        (y-coordinate (upper-right rectangle))))

BoxArea :
  ConcreteRealOperations ->
  Box ->
  Real
BoxArea operations rectangle =
  multiplyR operations
    (subtractR operations
      (x-coordinate (upper-right rectangle))
      (x-coordinate (lower-left rectangle)))
    (subtractR operations
      (y-coordinate (upper-right rectangle))
      (y-coordinate (lower-left rectangle)))

record TaggedBoxDivision : Set where
  constructor taggedBoxDivision
  field
    box-count     : Nat
    division-box  : Nat -> Box
    box-tag       : Nat -> Point

open TaggedBoxDivision public

BoxesInteriorDisjoint : Box -> Box -> Set
BoxesInteriorDisjoint firstBox secondBox =
  (p : Point) ->
  PointInBoxInterior firstBox p ->
  PointInBoxInterior secondBox p ->
  Bottom

TaggedBoxDivisionOf :
  Box ->
  TaggedBoxDivision ->
  Set
TaggedBoxDivisionOf outer division =
  Both
    ((i : Nat) ->
      i <N box-count division ->
      Both
        (ValidBox (division-box division i))
        (Both
          ((p : Point) ->
            PointInBox (division-box division i) p ->
            PointInBox outer p)
          (PointInBox
            (division-box division i)
            (box-tag division i))))
    (Both
      ((p : Point) ->
        PointInBox outer p ->
        Exists Nat
          (\ i ->
            Both
              (i <N box-count division)
              (PointInBox (division-box division i) p)))
      ((i j : Nat) ->
        i <N box-count division ->
        j <N box-count division ->
        i != j ->
        BoxesInteriorDisjoint
          (division-box division i)
          (division-box division j)))

Gauge2 : Set
Gauge2 = Point -> Real

PositiveGauge2 : Gauge2 -> Set
PositiveGauge2 gauge =
  (p : Point) -> Positive (gauge p)

GaugeFine2 :
  ConcreteRealOperations ->
  Gauge2 ->
  TaggedBoxDivision ->
  Set
GaugeFine2 operations gauge division =
  (i : Nat) ->
  i <N box-count division ->
  (p : Point) ->
  PointInBox (division-box division i) p ->
  PointClose
    operations
    p
    (box-tag division i)
    (gauge (box-tag division i))

riemannSum2 :
  ConcreteRealOperations ->
  (Point -> Real) ->
  TaggedBoxDivision ->
  Real
riemannSum2 operations integrand division =
  sumReals operations
    (\ i ->
      multiplyR operations
        (integrand (box-tag division i))
        (BoxArea operations (division-box division i)))
    (box-count division)

HasBoxIntegral :
  ConcreteRealOperations ->
  (Point -> Real) ->
  Box ->
  Real ->
  Set
HasBoxIntegral operations integrand outer integral =
  ValidBox outer ->
  (epsilon : Real) ->
  Positive epsilon ->
  Exists Gauge2
    (\ gauge ->
      Both
        (PositiveGauge2 gauge)
        ((division : TaggedBoxDivision) ->
          TaggedBoxDivisionOf outer division ->
          GaugeFine2 operations gauge division ->
          RealStrictLess
            (realDistance operations
              (riemannSum2 operations integrand division)
              integral)
            epsilon))

record RegionRestriction
  (operations : ConcreteRealOperations)
  (integrand : Point -> Real)
  (region : Region) : Set where
  field
    restrictedValue : Point -> Real
    value-on-region :
      (p : Point) ->
      region p ->
      RealEquivalent (restrictedValue p) (integrand p)
    zero-off-region :
      (p : Point) ->
      Not (region p) ->
      RealEquivalent (restrictedValue p) (zeroR operations)

open RegionRestriction

HasRegionIntegral :
  ConcreteRealOperations ->
  (Point -> Real) ->
  Region ->
  Real ->
  Set
HasRegionIntegral operations integrand region integral =
  Exists Box
    (\ outer ->
      Both
        (ValidBox outer)
        (Both
          ((p : Point) ->
            region p ->
            PointInBox outer p)
          (Exists
            (RegionRestriction operations integrand region)
            (\ restriction ->
              HasBoxIntegral operations
                (restrictedValue restriction)
                outer
                integral))))

WindingDensity :
  (operations : ConcreteRealOperations) ->
  DerivativeSelections operations ->
  Curve ->
  Point ->
  Real ->
  Real
WindingDensity operations selections g z t =
  divideR operations
    (subtractR operations
      (multiplyR operations
        (subtractR operations
          (x-coordinate (curveValue g t))
          (x-coordinate z))
        (y-coordinate
          (vectorDerivative selections g t)))
      (multiplyR operations
        (subtractR operations
          (y-coordinate (curveValue g t))
          (y-coordinate z))
        (x-coordinate
          (vectorDerivative selections g t))))
    (pointDistanceSquared operations (curveValue g t) z)

WindingNumberOne :
  (operations : ConcreteRealOperations) ->
  DerivativeSelections operations ->
  Curve ->
  Point ->
  Set
WindingNumberOne operations selections g z =
  HasIntervalIntegral operations
    (WindingDensity operations selections g z)
    (zeroR operations)
    (oneR operations)
    (twoPi operations)

curlDensity :
  (operations : ConcreteRealOperations) ->
  DerivativeSelections operations ->
  VectorField ->
  Point ->
  Real
curlDensity operations selections f z =
  subtractR operations
    (entry11 (frechetDerivative selections f z))
    (entry22 (frechetDerivative selections f z))

boundaryDensity :
  (operations : ConcreteRealOperations) ->
  DerivativeSelections operations ->
  VectorField ->
  Curve ->
  Real ->
  Real
boundaryDensity operations selections f g t =
  addR operations
    (multiplyR operations
      (y-coordinate (fieldValue f (curveValue g t)))
      (x-coordinate (vectorDerivative selections g t)))
    (multiplyR operations
      (x-coordinate (fieldValue f (curveValue g t)))
      (y-coordinate (vectorDerivative selections g t)))

derivativeAction :
  (operations : ConcreteRealOperations) ->
  DerivativeSelections operations ->
  VectorField ->
  Point ->
  Point ->
  Point
derivativeAction operations selections f h z =
  applyMatrix operations
    (frechetDerivative selections f z)
    h

green-s-theorem : Set1
green-s-theorem =
  (operations : ConcreteRealOperations) ->
  (selections : DerivativeSelections operations) ->
  (f : VectorField) ->
  (g : Curve) ->
  (u : Region) ->
  AbsolutelyContinuousOnUnit operations g ->
  PointEquivalent
    (curveValue g (oneR operations))
    (curveValue g (zeroR operations)) ->
  ((z : Point) ->
    Inside operations (pathImage operations g) z ->
    WindingNumberOne operations selections g z) ->
  OpenRegion operations u ->
  Subset
    (Union
      (Inside operations (pathImage operations g))
      (pathImage operations g))
    u ->
  DifferentiableOn operations f u ->
  ((h : Point) ->
    ContinuousVectorOn operations
      (derivativeAction operations selections f h)
      u) ->
  Exists Real
    (\ regionIntegral ->
      Exists Real
        (\ boundaryIntegral ->
          Both
            (HasRegionIntegral operations
              (curlDensity operations selections f)
              (Inside operations (pathImage operations g))
              regionIntegral)
            (Both
              (HasIntervalIntegral operations
                (boundaryDensity operations selections f g)
                (zeroR operations)
                (oneR operations)
                boundaryIntegral)
              (RealEquivalent boundaryIntegral regionIntegral))))
