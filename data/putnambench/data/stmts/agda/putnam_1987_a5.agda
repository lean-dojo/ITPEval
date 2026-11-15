-- Statement-only formalization of PutnamBench corpus artifact putnam_1987_a5:
-- nonexistence of a continuously partially differentiable curl-free real
-- vector field off the origin with the prescribed trace on the xy-plane.
-- This file contains no proof.

{-# OPTIONS --safe #-}

open import Agda.Builtin.Equality renaming (_≡_ to _==_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)

infix 4 _!=_
infixr 3 _and_
infixr 2 _or_

data Bottom : Set where

Not : Set -> Set
Not A =
  A -> Bottom

_!=_ : {A : Set} -> A -> A -> Set
x != y =
  Not (x == y)

record _and_ (A B : Set) : Set where
  constructor both
  field
    first  : A
    second : B

data _or_ (A B : Set) : Set where
  left  : A -> A or B
  right : B -> A or B

record Iff (A B : Set) : Set where
  constructor equivalence
  field
    forward  : A -> B
    backward : B -> A

record Exists (A : Set) (P : A -> Set) : Set where
  constructor witness
  field
    value    : A
    property : P value

record CompleteOrderedRealField (R : Set) : Set1 where
  field
    zeroR oneR : R
    add multiply : R -> R -> R
    negate inverse : R -> R
    lessOrEqual : R -> R -> Set
    fromNat : Nat -> R

    one-not-zero :
      oneR != zeroR

    add-commutative :
      (x y : R) -> add x y == add y x
    add-associative :
      (x y z : R) ->
      add (add x y) z == add x (add y z)
    add-zero :
      (x : R) -> add x zeroR == x
    add-inverse :
      (x : R) -> add x (negate x) == zeroR

    multiply-commutative :
      (x y : R) -> multiply x y == multiply y x
    multiply-associative :
      (x y z : R) ->
      multiply (multiply x y) z ==
      multiply x (multiply y z)
    multiply-one :
      (x : R) -> multiply x oneR == x
    multiply-zero :
      (x : R) -> multiply x zeroR == zeroR
    distribute :
      (x y z : R) ->
      multiply x (add y z) ==
      add (multiply x y) (multiply x z)
    inverse-zero :
      inverse zeroR == zeroR
    multiply-inverse :
      (x : R) ->
      x != zeroR ->
      multiply x (inverse x) == oneR

    order-reflexive :
      (x : R) -> lessOrEqual x x
    order-transitive :
      (x y z : R) ->
      lessOrEqual x y ->
      lessOrEqual y z ->
      lessOrEqual x z
    order-antisymmetric :
      (x y : R) ->
      lessOrEqual x y ->
      lessOrEqual y x ->
      x == y
    order-total :
      (x y : R) ->
      lessOrEqual x y or lessOrEqual y x
    add-order :
      (x y z : R) ->
      lessOrEqual x y ->
      lessOrEqual (add z x) (add z y)
    multiply-nonnegative :
      (x y : R) ->
      lessOrEqual zeroR x ->
      lessOrEqual zeroR y ->
      lessOrEqual zeroR (multiply x y)
    zero-less-than-one :
      lessOrEqual zeroR oneR and zeroR != oneR

    fromNat-zero :
      fromNat zero == zeroR
    fromNat-successor :
      (n : Nat) ->
      fromNat (suc n) == add (fromNat n) oneR
    fromNat-addition :
      (m n : Nat) ->
      fromNat (m + n) == add (fromNat m) (fromNat n)
    fromNat-multiplication :
      (m n : Nat) ->
      fromNat (m * n) == multiply (fromNat m) (fromNat n)
    fromNat-injective :
      (m n : Nat) ->
      fromNat m == fromNat n ->
      m == n

    archimedean :
      (x : R) ->
      Exists Nat
        (\ n ->
          lessOrEqual x (fromNat n))
    least-upper-bound :
      (P : R -> Set) ->
      Exists R P ->
      Exists R
        (\ upper ->
          (x : R) ->
          P x ->
          lessOrEqual x upper) ->
      Exists R
        (\ supremum ->
          ((x : R) ->
            P x ->
            lessOrEqual x supremum)
          and
          ((upper : R) ->
            ((x : R) ->
              P x ->
              lessOrEqual x upper) ->
            lessOrEqual supremum upper))

open CompleteOrderedRealField

fourN : Nat
fourN =
  suc (suc (suc (suc zero)))

subtract :
  {R : Set} ->
  CompleteOrderedRealField R ->
  R ->
  R ->
  R
subtract reals x y =
  add reals x (negate reals y)

divide :
  {R : Set} ->
  CompleteOrderedRealField R ->
  R ->
  R ->
  R
divide reals x y =
  multiply reals x (inverse reals y)

square :
  {R : Set} ->
  CompleteOrderedRealField R ->
  R ->
  R
square reals x =
  multiply reals x x

StrictLess :
  {R : Set} ->
  CompleteOrderedRealField R ->
  R ->
  R ->
  Set
StrictLess reals x y =
  lessOrEqual reals x y and x != y

CloseTo :
  {R : Set} ->
  CompleteOrderedRealField R ->
  R ->
  R ->
  R ->
  Set
CloseTo reals center radius x =
  StrictLess reals
    (subtract reals center radius)
    x
  and
  StrictLess reals
    x
    (add reals center radius)

differenceQuotient :
  {R : Set} ->
  CompleteOrderedRealField R ->
  (R -> R) ->
  R ->
  R ->
  R
differenceQuotient reals function point x =
  divide reals
    (subtract reals (function x) (function point))
    (subtract reals x point)

DerivativeAt :
  {R : Set} ->
  CompleteOrderedRealField R ->
  (R -> R) ->
  R ->
  R ->
  Set
DerivativeAt {R} reals function point derivativeValue =
  (epsilon : R) ->
  StrictLess reals (zeroR reals) epsilon ->
  Exists R
    (\ delta ->
      StrictLess reals (zeroR reals) delta
      and
      ((x : R) ->
        CloseTo reals point delta x ->
        x != point ->
        CloseTo reals derivativeValue epsilon
          (differenceQuotient reals function point x)))

HasDerivativeAt :
  {R : Set} ->
  CompleteOrderedRealField R ->
  (R -> R) ->
  R ->
  Set
HasDerivativeAt {R} reals function point =
  Exists R
    (\ derivativeValue ->
      DerivativeAt reals function point derivativeValue)

record StandardRealCalculus
  {R : Set}
  (reals : CompleteOrderedRealField R) : Set1 where

  field
    derivative : (R -> R) -> R -> R

    derivative-when-differentiable :
      (function : R -> R) ->
      (point : R) ->
      HasDerivativeAt reals function point ->
      DerivativeAt reals
        function
        point
        (derivative function point)

    derivative-when-not-differentiable :
      (function : R -> R) ->
      (point : R) ->
      Not (HasDerivativeAt reals function point) ->
      derivative function point == zeroR reals

open StandardRealCalculus

record Vector3 (R : Set) : Set where
  constructor vector3
  field
    xCoordinate : R
    yCoordinate : R
    zCoordinate : R

open Vector3

zeroVector3 :
  {R : Set} ->
  CompleteOrderedRealField R ->
  Vector3 R
zeroVector3 reals =
  vector3
    (zeroR reals)
    (zeroR reals)
    (zeroR reals)

replaceX :
  {R : Set} ->
  Vector3 R ->
  R ->
  Vector3 R
replaceX point x =
  vector3 x (yCoordinate point) (zCoordinate point)

replaceY :
  {R : Set} ->
  Vector3 R ->
  R ->
  Vector3 R
replaceY point y =
  vector3 (xCoordinate point) y (zCoordinate point)

replaceZ :
  {R : Set} ->
  Vector3 R ->
  R ->
  Vector3 R
replaceZ point z =
  vector3 (xCoordinate point) (yCoordinate point) z

VectorClose :
  {R : Set} ->
  CompleteOrderedRealField R ->
  Vector3 R ->
  R ->
  Vector3 R ->
  Set
VectorClose reals center radius point =
  CloseTo reals
    (xCoordinate center)
    radius
    (xCoordinate point)
  and
  CloseTo reals
    (yCoordinate center)
    radius
    (yCoordinate point)
  and
  CloseTo reals
    (zCoordinate center)
    radius
    (zCoordinate point)

Punctured :
  {R : Set} ->
  CompleteOrderedRealField R ->
  Vector3 R ->
  Set
Punctured reals point =
  point != zeroVector3 reals

ContinuousOnPuncturedAt :
  {R : Set} ->
  CompleteOrderedRealField R ->
  (Vector3 R -> R) ->
  Vector3 R ->
  Set
ContinuousOnPuncturedAt {R} reals function point =
  Punctured reals point ->
  (epsilon : R) ->
  StrictLess reals (zeroR reals) epsilon ->
  Exists R
    (\ delta ->
      StrictLess reals (zeroR reals) delta
      and
      ((nearby : Vector3 R) ->
        Punctured reals nearby ->
        VectorClose reals point delta nearby ->
        CloseTo reals
          (function point)
          epsilon
          (function nearby)))

ContinuousOnPunctured :
  {R : Set} ->
  CompleteOrderedRealField R ->
  (Vector3 R -> R) ->
  Set
ContinuousOnPunctured {R} reals function =
  (point : Vector3 R) ->
  ContinuousOnPuncturedAt reals function point

partialX :
  {R : Set} ->
  (reals : CompleteOrderedRealField R) ->
  StandardRealCalculus reals ->
  (Vector3 R -> R) ->
  Vector3 R ->
  R
partialX reals calculus function point =
  derivative calculus
    (\ x -> function (replaceX point x))
    (xCoordinate point)

partialY :
  {R : Set} ->
  (reals : CompleteOrderedRealField R) ->
  StandardRealCalculus reals ->
  (Vector3 R -> R) ->
  Vector3 R ->
  R
partialY reals calculus function point =
  derivative calculus
    (\ y -> function (replaceY point y))
    (yCoordinate point)

partialZ :
  {R : Set} ->
  (reals : CompleteOrderedRealField R) ->
  StandardRealCalculus reals ->
  (Vector3 R -> R) ->
  Vector3 R ->
  R
partialZ reals calculus function point =
  derivative calculus
    (\ z -> function (replaceZ point z))
    (zCoordinate point)

HasPartialXAt :
  {R : Set} ->
  CompleteOrderedRealField R ->
  (Vector3 R -> R) ->
  Vector3 R ->
  Set
HasPartialXAt reals function point =
  HasDerivativeAt reals
    (\ x -> function (replaceX point x))
    (xCoordinate point)

HasPartialYAt :
  {R : Set} ->
  CompleteOrderedRealField R ->
  (Vector3 R -> R) ->
  Vector3 R ->
  Set
HasPartialYAt reals function point =
  HasDerivativeAt reals
    (\ y -> function (replaceY point y))
    (yCoordinate point)

HasPartialZAt :
  {R : Set} ->
  CompleteOrderedRealField R ->
  (Vector3 R -> R) ->
  Vector3 R ->
  Set
HasPartialZAt reals function point =
  HasDerivativeAt reals
    (\ z -> function (replaceZ point z))
    (zCoordinate point)

HasContinuousPartialsOffOrigin :
  {R : Set} ->
  (reals : CompleteOrderedRealField R) ->
  StandardRealCalculus reals ->
  (Vector3 R -> R) ->
  Set
HasContinuousPartialsOffOrigin {R} reals calculus function =
  ((point : Vector3 R) ->
    Punctured reals point ->
    HasPartialXAt reals function point
    and
    HasPartialYAt reals function point
    and
    HasPartialZAt reals function point)
  and
  ContinuousOnPunctured reals
    (partialX reals calculus function)
  and
  ContinuousOnPunctured reals
    (partialY reals calculus function)
  and
  ContinuousOnPunctured reals
    (partialZ reals calculus function)

VectorField :
  Set ->
  Set
VectorField R =
  Vector3 R -> Vector3 R

firstComponent :
  {R : Set} ->
  VectorField R ->
  Vector3 R ->
  R
firstComponent vectorField point =
  xCoordinate (vectorField point)

secondComponent :
  {R : Set} ->
  VectorField R ->
  Vector3 R ->
  R
secondComponent vectorField point =
  yCoordinate (vectorField point)

thirdComponent :
  {R : Set} ->
  VectorField R ->
  Vector3 R ->
  R
thirdComponent vectorField point =
  zCoordinate (vectorField point)

VectorFieldHasContinuousPartialsOffOrigin :
  {R : Set} ->
  (reals : CompleteOrderedRealField R) ->
  StandardRealCalculus reals ->
  VectorField R ->
  Set
VectorFieldHasContinuousPartialsOffOrigin reals calculus vectorField =
  HasContinuousPartialsOffOrigin reals calculus
    (firstComponent vectorField)
  and
  HasContinuousPartialsOffOrigin reals calculus
    (secondComponent vectorField)
  and
  HasContinuousPartialsOffOrigin reals calculus
    (thirdComponent vectorField)

CurlFreeOffOrigin :
  {R : Set} ->
  (reals : CompleteOrderedRealField R) ->
  StandardRealCalculus reals ->
  VectorField R ->
  Set
CurlFreeOffOrigin {R} reals calculus vectorField =
  (point : Vector3 R) ->
  Punctured reals point ->
  subtract reals
    (partialY reals calculus (thirdComponent vectorField) point)
    (partialZ reals calculus (secondComponent vectorField) point)
  ==
  zeroR reals
  and
  subtract reals
    (partialZ reals calculus (firstComponent vectorField) point)
    (partialX reals calculus (thirdComponent vectorField) point)
  ==
  zeroR reals
  and
  subtract reals
    (partialX reals calculus (secondComponent vectorField) point)
    (partialY reals calculus (firstComponent vectorField) point)
  ==
  zeroR reals

prescribedDenominator :
  {R : Set} ->
  CompleteOrderedRealField R ->
  R ->
  R ->
  R
prescribedDenominator reals x y =
  add reals
    (square reals x)
    (multiply reals
      (fromNat reals fourN)
      (square reals y))

prescribedTrace :
  {R : Set} ->
  CompleteOrderedRealField R ->
  R ->
  R ->
  Vector3 R
prescribedTrace reals x y =
  vector3
    (divide reals
      (negate reals y)
      (prescribedDenominator reals x y))
    (divide reals
      x
      (prescribedDenominator reals x y))
    (zeroR reals)

HasPrescribedTrace :
  {R : Set} ->
  CompleteOrderedRealField R ->
  VectorField R ->
  Set
HasPrescribedTrace {R} reals vectorField =
  (x y : R) ->
  vectorField (vector3 x y (zeroR reals)) ==
  prescribedTrace reals x y

Putnam1987A5Existence :
  {R : Set} ->
  (reals : CompleteOrderedRealField R) ->
  StandardRealCalculus reals ->
  Set
Putnam1987A5Existence {R} reals calculus =
  Exists (VectorField R)
    (\ vectorField ->
      VectorFieldHasContinuousPartialsOffOrigin
        reals calculus vectorField
      and
      CurlFreeOffOrigin reals calculus vectorField
      and
      HasPrescribedTrace reals vectorField)

putnam-1987-a5 : Set1
putnam-1987-a5 =
  (R : Set) ->
  (reals : CompleteOrderedRealField R) ->
  (calculus : StandardRealCalculus reals) ->
  Iff
    (Putnam1987A5Existence reals calculus)
    Bottom
