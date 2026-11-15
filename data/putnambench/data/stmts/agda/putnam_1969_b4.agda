-- Statement-only formalization of PutnamBench corpus artifact putnam_1969_b4:
-- every continuous plane curve of length one is covered by a closed rectangle
-- of area one quarter. This file contains no proof.

{-# OPTIONS --safe #-}

open import Agda.Builtin.Equality renaming (_≡_ to _==_)
open import Agda.Builtin.Nat using (Nat; zero; suc)

infix 4 _!=_ _<N_
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

record Exists (A : Set) (P : A -> Set) : Set where
  constructor witness
  field
    value    : A
    property : P value

data _<N_ : Nat -> Nat -> Set where
  zero<suc : {n : Nat} -> zero <N suc n
  suc<suc  : {m n : Nat} -> m <N n -> suc m <N suc n

one : Nat
one =
  suc zero

two : Nat
two =
  suc one

three : Nat
three =
  suc two

four : Nat
four =
  suc three

record CompleteOrderedRealField (R : Set) : Set1 where
  field
    zeroR oneR : R
    add multiply : R -> R -> R
    negate inverse squareRoot : R -> R
    lessOrEqual : R -> R -> Set
    fromNat : Nat -> R

    one-not-zero :
      oneR != zeroR

    add-commutative :
      (x y : R) -> add x y == add y x
    add-associative :
      (x y z : R) -> add (add x y) z == add x (add y z)
    add-zero :
      (x : R) -> add x zeroR == x
    add-inverse :
      (x : R) -> add x (negate x) == zeroR

    multiply-commutative :
      (x y : R) -> multiply x y == multiply y x
    multiply-associative :
      (x y z : R) ->
      multiply (multiply x y) z == multiply x (multiply y z)
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
      (n : Nat) -> fromNat (suc n) == add (fromNat n) oneR

    archimedean :
      (x : R) ->
      Exists Nat (\ n -> lessOrEqual x (fromNat n))
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
          ((x : R) -> P x -> lessOrEqual x supremum)
          and
          ((upper : R) ->
            ((x : R) -> P x -> lessOrEqual x upper) ->
            lessOrEqual supremum upper))

    square-root-nonnegative :
      (x : R) ->
      lessOrEqual zeroR (squareRoot x)
    square-root-square :
      (x : R) ->
      lessOrEqual zeroR x ->
      multiply (squareRoot x) (squareRoot x) == x
    square-root-nonpositive :
      (x : R) ->
      lessOrEqual x zeroR ->
      squareRoot x == zeroR

open CompleteOrderedRealField

subtract :
  {R : Set} ->
  CompleteOrderedRealField R ->
  R ->
  R ->
  R
subtract reals x y =
  add reals x (negate reals y)

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

Nonnegative :
  {R : Set} ->
  CompleteOrderedRealField R ->
  R ->
  Set
Nonnegative reals x =
  lessOrEqual reals (zeroR reals) x

UnitInterval :
  {R : Set} ->
  CompleteOrderedRealField R ->
  R ->
  Set
UnitInterval reals x =
  lessOrEqual reals (zeroR reals) x
  and
  lessOrEqual reals x (oneR reals)

realDistance :
  {R : Set} ->
  CompleteOrderedRealField R ->
  R ->
  R ->
  R
realDistance reals x y =
  squareRoot reals (square reals (subtract reals x y))

record Point (R : Set) : Set where
  constructor point
  field
    x-coordinate : R
    y-coordinate : R

open Point

PointEqual :
  {R : Set} ->
  Point R ->
  Point R ->
  Set
PointEqual p q =
  x-coordinate p == x-coordinate q
  and
  y-coordinate p == y-coordinate q

squaredDistance :
  {R : Set} ->
  CompleteOrderedRealField R ->
  Point R ->
  Point R ->
  R
squaredDistance reals p q =
  add reals
    (square reals
      (subtract reals (x-coordinate p) (x-coordinate q)))
    (square reals
      (subtract reals (y-coordinate p) (y-coordinate q)))

pointDistance :
  {R : Set} ->
  CompleteOrderedRealField R ->
  Point R ->
  Point R ->
  R
pointDistance reals p q =
  squareRoot reals (squaredDistance reals p q)

ContinuousOnUnitInterval :
  {R : Set} ->
  CompleteOrderedRealField R ->
  (R -> Point R) ->
  Set
ContinuousOnUnitInterval {R} reals curve =
  (t : R) ->
  UnitInterval reals t ->
  (epsilon : R) ->
  StrictLess reals (zeroR reals) epsilon ->
  Exists R
    (\ delta ->
      StrictLess reals (zeroR reals) delta
      and
      ((s : R) ->
        UnitInterval reals s ->
        StrictLess reals (realDistance reals s t) delta ->
        StrictLess reals
          (pointDistance reals (curve s) (curve t))
          epsilon))

module Putnam1969B4Statement
  {R : Set}
  (reals : CompleteOrderedRealField R) where

  Curve : Set
  Curve =
    R -> Point R

  record Partition : Set where
    constructor partition
    field
      count : Nat
      parameter : Nat -> R
      begins-at-zero :
        parameter zero == zeroR reals
      ends-at-one :
        parameter count == oneR reals
      increasing :
        (i : Nat) ->
        i <N count ->
        lessOrEqual reals
          (parameter i)
          (parameter (suc i))

  open Partition

  distanceSum :
    Curve ->
    (Nat -> R) ->
    Nat ->
    R
  distanceSum curve parameters zero =
    zeroR reals
  distanceSum curve parameters (suc n) =
    add reals
      (distanceSum curve parameters n)
      (pointDistance reals
        (curve (parameters n))
        (curve (parameters (suc n))))

  partitionLength :
    Curve ->
    Partition ->
    R
  partitionLength curve p =
    distanceSum curve (parameter p) (count p)

  UpperLengthBound :
    Curve ->
    R ->
    Set
  UpperLengthBound curve bound =
    (p : Partition) ->
    lessOrEqual reals (partitionLength curve p) bound

  PathLength :
    Curve ->
    R ->
    Set
  PathLength curve length =
    UpperLengthBound curve length
    and
    ((bound : R) ->
      UpperLengthBound curve bound ->
      lessOrEqual reals length bound)

  record ConvexWeights : Set where
    constructor weights
    field
      alpha beta gamma delta : R

  open ConvexWeights

  weightSum :
    ConvexWeights ->
    R
  weightSum w =
    add reals
      (alpha w)
      (add reals
        (beta w)
        (add reals (gamma w) (delta w)))

  weightedPoint :
    ConvexWeights ->
    Point R ->
    Point R ->
    Point R ->
    Point R ->
    Point R
  weightedPoint w a b c d =
    point
      (add reals
        (multiply reals (alpha w) (x-coordinate a))
        (add reals
          (multiply reals (beta w) (x-coordinate b))
          (add reals
            (multiply reals (gamma w) (x-coordinate c))
            (multiply reals (delta w) (x-coordinate d)))))
      (add reals
        (multiply reals (alpha w) (y-coordinate a))
        (add reals
          (multiply reals (beta w) (y-coordinate b))
          (add reals
            (multiply reals (gamma w) (y-coordinate c))
            (multiply reals (delta w) (y-coordinate d)))))

  ConvexHull4 :
    Point R ->
    Point R ->
    Point R ->
    Point R ->
    Point R ->
    Set
  ConvexHull4 a b c d p =
    Exists ConvexWeights
      (\ w ->
        Nonnegative reals (alpha w)
        and
        Nonnegative reals (beta w)
        and
        Nonnegative reals (gamma w)
        and
        Nonnegative reals (delta w)
        and
        weightSum w == oneR reals
        and
        PointEqual p (weightedPoint w a b c d))

  dotAt :
    Point R ->
    Point R ->
    Point R ->
    R
  dotAt a vertex c =
    add reals
      (multiply reals
        (subtract reals (x-coordinate a) (x-coordinate vertex))
        (subtract reals (x-coordinate c) (x-coordinate vertex)))
      (multiply reals
        (subtract reals (y-coordinate a) (y-coordinate vertex))
        (subtract reals (y-coordinate c) (y-coordinate vertex)))

  RightAngle :
    Point R ->
    Point R ->
    Point R ->
    Set
  RightAngle a vertex c =
    Not (PointEqual a vertex)
    and
    Not (PointEqual c vertex)
    and
    dotAt a vertex c == zeroR reals

  oneQuarter : R
  oneQuarter =
    multiply reals
      (oneR reals)
      (inverse reals (fromNat reals four))

  CoveredByRectangle :
    Curve ->
    Point R ->
    Point R ->
    Point R ->
    Point R ->
    Set
  CoveredByRectangle curve a b c d =
    ((t : R) ->
      UnitInterval reals t ->
      ConvexHull4 a b c d (curve t))
    and
    multiply reals
      (pointDistance reals a b)
      (pointDistance reals b c)
      == oneQuarter
    and
    RightAngle a b c
    and
    RightAngle b c d
    and
    RightAngle c d a
    and
    RightAngle d a b

  proposition : Set
  proposition =
    (curve : Curve) ->
    ContinuousOnUnitInterval reals curve ->
    PathLength curve (oneR reals) ->
    Exists (Point R)
      (\ a ->
        Exists (Point R)
          (\ b ->
            Exists (Point R)
              (\ c ->
                Exists (Point R)
                  (\ d ->
                    CoveredByRectangle curve a b c d))))

putnam-1969-b4 : Set1
putnam-1969-b4 =
  (R : Set) ->
  (reals : CompleteOrderedRealField R) ->
  Putnam1969B4Statement.proposition reals
