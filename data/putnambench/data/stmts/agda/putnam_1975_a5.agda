-- Statement-only formalization of PutnamBench corpus artifact putnam_1975_a5:
-- positive linearly independent solutions of y'' = f(x)y on a real interval
-- yield a scaled geometric mean satisfying z'' + 1/z^3 = f(x)z there. This
-- file contains no proof.

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

record Exists (A : Set) (P : A -> Set) : Set where
  constructor witness
  field
    value    : A
    property : P value

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
          ((x : R) ->
            P x ->
            lessOrEqual x supremum)
          and
          ((upper : R) ->
            ((x : R) ->
              P x ->
              lessOrEqual x upper) ->
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
    square-root-unique :
      (x y : R) ->
      lessOrEqual zeroR y ->
      multiply y y == x ->
      y == squareRoot x

open CompleteOrderedRealField

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

cube :
  {R : Set} ->
  CompleteOrderedRealField R ->
  R ->
  R
cube reals x =
  multiply reals (multiply reals x x) x

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

ContinuousAt :
  {R : Set} ->
  CompleteOrderedRealField R ->
  (R -> R) ->
  R ->
  Set
ContinuousAt {R} reals function point =
  (epsilon : R) ->
  StrictLess reals (zeroR reals) epsilon ->
  Exists R
    (\ delta ->
      StrictLess reals (zeroR reals) delta
      and
      ((x : R) ->
        CloseTo reals point delta x ->
        CloseTo reals
          (function point)
          epsilon
          (function x)))

Continuous :
  {R : Set} ->
  CompleteOrderedRealField R ->
  (R -> R) ->
  Set
Continuous {R} reals function =
  (point : R) ->
  ContinuousAt reals function point

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
DerivativeAt {R} reals function point derivative =
  (epsilon : R) ->
  StrictLess reals (zeroR reals) epsilon ->
  Exists R
    (\ delta ->
      StrictLess reals (zeroR reals) delta
      and
      ((x : R) ->
        CloseTo reals point delta x ->
        x != point ->
        CloseTo reals derivative epsilon
          (differenceQuotient reals function point x)))

ContinuousSecondOrderSolution :
  {R : Set} ->
  CompleteOrderedRealField R ->
  (R -> R) ->
  (R -> R) ->
  Set
ContinuousSecondOrderSolution {R} reals coefficient function =
  Exists (R -> R)
    (\ firstDerivative ->
      Exists (R -> R)
        (\ secondDerivative ->
          ((x : R) ->
            DerivativeAt reals
              function
              x
              (firstDerivative x))
          and
          ((x : R) ->
            DerivativeAt reals
              firstDerivative
              x
              (secondDerivative x))
          and
          Continuous reals function
          and
          Continuous reals firstDerivative
          and
          Continuous reals secondDerivative
          and
          ((x : R) ->
            secondDerivative x ==
            multiply reals
              (coefficient x)
              (function x))))

SecondDerivativeAt :
  {R : Set} ->
  CompleteOrderedRealField R ->
  (R -> R) ->
  R ->
  R ->
  Set
SecondDerivativeAt {R} reals function point secondDerivative =
  Exists (R -> R)
    (\ firstDerivative ->
      Exists R
        (\ radius ->
          StrictLess reals (zeroR reals) radius
          and
          (((x : R) ->
            CloseTo reals point radius x ->
            DerivativeAt reals
              function
              x
              (firstDerivative x))
          and
          DerivativeAt reals
            firstDerivative
            point
            secondDerivative)))

record RealInterval
  {R : Set}
  (reals : CompleteOrderedRealField R) :
  Set1 where

  field
    contains : R -> Set

    order-convex :
      (x y z : R) ->
      contains x ->
      contains y ->
      lessOrEqual reals x z ->
      lessOrEqual reals z y ->
      contains z

open RealInterval

LinearlyIndependent :
  {R : Set} ->
  CompleteOrderedRealField R ->
  (R -> R) ->
  (R -> R) ->
  Set
LinearlyIndependent {R} reals y1 y2 =
  (c1 c2 : R) ->
  ((x : R) ->
    add reals
      (multiply reals c1 (y1 x))
      (multiply reals c2 (y2 x))
    ==
    zeroR reals) ->
  c1 == zeroR reals and c2 == zeroR reals

PositiveOn :
  {R : Set} ->
  (reals : CompleteOrderedRealField R) ->
  RealInterval reals ->
  (R -> R) ->
  Set
PositiveOn {R} reals interval function =
  (x : R) ->
  contains interval x ->
  StrictLess reals (zeroR reals) (function x)

scaledGeometricMean :
  {R : Set} ->
  CompleteOrderedRealField R ->
  R ->
  (R -> R) ->
  (R -> R) ->
  R ->
  R
scaledGeometricMean reals c y1 y2 x =
  multiply reals c
    (squareRoot reals
      (multiply reals (y1 x) (y2 x)))

SatisfiesNonlinearEquationAt :
  {R : Set} ->
  CompleteOrderedRealField R ->
  (R -> R) ->
  (R -> R) ->
  R ->
  Set
SatisfiesNonlinearEquationAt {R} reals coefficient function x =
  Exists R
    (\ secondDerivative ->
      SecondDerivativeAt reals
        function
        x
        secondDerivative
      and
      add reals
        secondDerivative
        (divide reals
          (oneR reals)
          (cube reals (function x)))
      ==
      multiply reals
        (coefficient x)
        (function x))

module Putnam1975A5Statement
  {R : Set}
  (reals : CompleteOrderedRealField R) where

  proposition : Set1
  proposition =
    (interval : RealInterval reals) ->
    (f y1 y2 : R -> R) ->
    Continuous reals f ->
    ContinuousSecondOrderSolution reals f y1 ->
    ContinuousSecondOrderSolution reals f y2 ->
    LinearlyIndependent reals y1 y2 ->
    PositiveOn reals interval y1 ->
    PositiveOn reals interval y2 ->
    Exists R
      (\ c ->
        StrictLess reals (zeroR reals) c
        and
        ((x : R) ->
          contains interval x ->
          SatisfiesNonlinearEquationAt reals
            f
            (scaledGeometricMean reals c y1 y2)
            x))

putnam-1975-a5 : Set1
putnam-1975-a5 =
  (R : Set) ->
  (reals : CompleteOrderedRealField R) ->
  Putnam1975A5Statement.proposition reals
