-- Statement-only formalization of PutnamBench corpus artifact putnam_2021_b3
-- (putnambench__agda__putnam_2021_b3): vanishing of the integral of
-- y*h_x - x*h_y over a suitably centered disk. This file contains no proof.

{-# OPTIONS --safe #-}

module Main where

open import Agda.Builtin.Equality renaming (_≡_ to _==_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)

infix 4 _!=_ _<=N_
infixr 3 _and_
infixr 2 _or_

data Bottom : Set where

record Top : Set where
  constructor top

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

data _<=N_ : Nat -> Nat -> Set where
  zero<=N   : {n : Nat} -> zero <=N n
  suc<=sucN : {m n : Nat} -> m <=N n -> suc m <=N suc n

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

oneN : Nat
oneN =
  suc zero

twoN : Nat
twoN =
  suc oneN

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

sumFirst :
  {R : Set} ->
  CompleteOrderedRealField R ->
  Nat ->
  (Nat -> R) ->
  R
sumFirst reals zero terms =
  zeroR reals
sumFirst reals (suc n) terms =
  add reals
    (sumFirst reals n terms)
    (terms n)

ConvergesTo :
  {R : Set} ->
  CompleteOrderedRealField R ->
  (Nat -> R) ->
  R ->
  Set
ConvergesTo {R} reals sequence limit =
  (epsilon : R) ->
  StrictLess reals (zeroR reals) epsilon ->
  Exists Nat
    (\ cutoff ->
      (n : Nat) ->
      cutoff <=N n ->
      CloseTo reals limit epsilon (sequence n))

naturalPower :
  {R : Set} ->
  CompleteOrderedRealField R ->
  R ->
  Nat ->
  R
naturalPower reals x zero =
  oneR reals
naturalPower reals x (suc n) =
  multiply reals
    (naturalPower reals x n)
    x

factorial : Nat -> Nat
factorial zero =
  oneN
factorial (suc n) =
  suc n * factorial n

alternate :
  {R : Set} ->
  CompleteOrderedRealField R ->
  Nat ->
  R ->
  R
alternate reals zero x =
  x
alternate reals (suc n) x =
  negate reals (alternate reals n x)

evenExponent : Nat -> Nat
evenExponent n =
  n + n

oddExponent : Nat -> Nat
oddExponent n =
  suc (evenExponent n)

sineTerm :
  {R : Set} ->
  CompleteOrderedRealField R ->
  R ->
  Nat ->
  R
sineTerm reals x n =
  alternate reals n
    (divide reals
      (naturalPower reals x (oddExponent n))
      (fromNat reals (factorial (oddExponent n))))

cosineTerm :
  {R : Set} ->
  CompleteOrderedRealField R ->
  R ->
  Nat ->
  R
cosineTerm reals x n =
  alternate reals n
    (divide reals
      (naturalPower reals x (evenExponent n))
      (fromNat reals (factorial (evenExponent n))))

SeriesHasSum :
  {R : Set} ->
  CompleteOrderedRealField R ->
  (Nat -> R) ->
  R ->
  Set
SeriesHasSum reals terms value =
  ConvergesTo reals
    (\ n -> sumFirst reals n terms)
    value

record StandardTrigonometry
  {R : Set}
  (reals : CompleteOrderedRealField R) :
  Set1 where

  field
    sine cosine : R -> R
    pi : R

    sine-is-power-series :
      (x : R) ->
      SeriesHasSum reals
        (sineTerm reals x)
        (sine x)
    cosine-is-power-series :
      (x : R) ->
      SeriesHasSum reals
        (cosineTerm reals x)
        (cosine x)
    pi-positive :
      StrictLess reals (zeroR reals) pi
    sine-pi-zero :
      sine pi == zeroR reals
    pi-is-first-positive-sine-zero :
      (x : R) ->
      StrictLess reals (zeroR reals) x ->
      sine x == zeroR reals ->
      lessOrEqual reals pi x

open StandardTrigonometry

rightRiemannSum :
  {R : Set} ->
  CompleteOrderedRealField R ->
  R ->
  R ->
  (R -> R) ->
  Nat ->
  R
rightRiemannSum reals lower upper function pieces =
  let
    step =
      divide reals
        (subtract reals upper lower)
        (fromNat reals pieces)
  in
  sumFirst reals pieces
    (\ i ->
      multiply reals
        (function
          (add reals lower
            (multiply reals
              (fromNat reals (suc i))
              step)))
        step)

IntervalIntegralValue :
  {R : Set} ->
  CompleteOrderedRealField R ->
  R ->
  R ->
  (R -> R) ->
  R ->
  Set
IntervalIntegralValue reals lower upper function value =
  ConvergesTo reals
    (\ n ->
      rightRiemannSum reals
        lower
        upper
        function
        (suc n))
    value

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
DerivativeAt {R} reals function point derivative-value =
  (epsilon : R) ->
  StrictLess reals (zeroR reals) epsilon ->
  Exists R
    (\ delta ->
      StrictLess reals (zeroR reals) delta
      and
      ((x : R) ->
        CloseTo reals point delta x ->
        x != point ->
        CloseTo reals derivative-value epsilon
          (differenceQuotient reals function point x)))

record Point2 (R : Set) : Set where
  constructor point2
  field
    firstCoordinate  : R
    secondCoordinate : R

open Point2

addPoint :
  {R : Set} ->
  CompleteOrderedRealField R ->
  Point2 R ->
  Point2 R ->
  Point2 R
addPoint reals p q =
  point2
    (add reals
      (firstCoordinate p)
      (firstCoordinate q))
    (add reals
      (secondCoordinate p)
      (secondCoordinate q))

squaredDistance :
  {R : Set} ->
  CompleteOrderedRealField R ->
  Point2 R ->
  Point2 R ->
  R
squaredDistance reals p q =
  add reals
    (square reals
      (subtract reals
        (firstCoordinate p)
        (firstCoordinate q)))
    (square reals
      (subtract reals
        (secondCoordinate p)
        (secondCoordinate q)))

ContinuousAt2 :
  {R : Set} ->
  CompleteOrderedRealField R ->
  (Point2 R -> R) ->
  Point2 R ->
  Set
ContinuousAt2 {R} reals function point =
  (epsilon : R) ->
  StrictLess reals (zeroR reals) epsilon ->
  Exists R
    (\ delta ->
      StrictLess reals (zeroR reals) delta
      and
      ((q : Point2 R) ->
        StrictLess reals
          (squaredDistance reals point q)
          (square reals delta) ->
        CloseTo reals
          (function point)
          epsilon
          (function q)))

Continuous2 :
  {R : Set} ->
  CompleteOrderedRealField R ->
  (Point2 R -> R) ->
  Set
Continuous2 {R} reals function =
  (point : Point2 R) ->
  ContinuousAt2 reals function point

record C2Data
  {R : Set}
  (reals : CompleteOrderedRealField R)
  (function : Point2 R -> R) :
  Set where

  field
    partialX partialY : Point2 R -> R
    partialXX partialXY partialYX partialYY : Point2 R -> R

    function-continuous :
      Continuous2 reals function
    partialX-continuous :
      Continuous2 reals partialX
    partialY-continuous :
      Continuous2 reals partialY
    partialXX-continuous :
      Continuous2 reals partialXX
    partialXY-continuous :
      Continuous2 reals partialXY
    partialYX-continuous :
      Continuous2 reals partialYX
    partialYY-continuous :
      Continuous2 reals partialYY

    partialX-is-derivative :
      (p : Point2 R) ->
      DerivativeAt reals
        (\ x ->
          function
            (point2 x (secondCoordinate p)))
        (firstCoordinate p)
        (partialX p)
    partialY-is-derivative :
      (p : Point2 R) ->
      DerivativeAt reals
        (\ y ->
          function
            (point2 (firstCoordinate p) y))
        (secondCoordinate p)
        (partialY p)
    partialXX-is-derivative :
      (p : Point2 R) ->
      DerivativeAt reals
        (\ x ->
          partialX
            (point2 x (secondCoordinate p)))
        (firstCoordinate p)
        (partialXX p)
    partialXY-is-derivative :
      (p : Point2 R) ->
      DerivativeAt reals
        (\ y ->
          partialX
            (point2 (firstCoordinate p) y))
        (secondCoordinate p)
        (partialXY p)
    partialYX-is-derivative :
      (p : Point2 R) ->
      DerivativeAt reals
        (\ x ->
          partialY
            (point2 x (secondCoordinate p)))
        (firstCoordinate p)
        (partialYX p)
    partialYY-is-derivative :
      (p : Point2 R) ->
      DerivativeAt reals
        (\ y ->
          partialY
            (point2 (firstCoordinate p) y))
        (secondCoordinate p)
        (partialYY p)

open C2Data

module Putnam2021B3Statement
  {R : Set}
  (reals : CompleteOrderedRealField R)
  (trigonometry : StandardTrigonometry reals) where

  origin : Point2 R
  origin =
    point2 (zeroR reals) (zeroR reals)

  twoPi : R
  twoPi =
    multiply reals
      (fromNat reals twoN)
      (pi trigonometry)

  polarOffset :
    R ->
    R ->
    Point2 R
  polarOffset radius angle =
    point2
      (multiply reals
        radius
        (cosine trigonometry angle))
      (multiply reals
        radius
        (sine trigonometry angle))

  angularDensity :
    (function : Point2 R -> R) ->
    C2Data reals function ->
    Point2 R ->
    R
  angularDensity function smooth p =
    subtract reals
      (multiply reals
        (secondCoordinate p)
        (partialX smooth p))
      (multiply reals
        (firstCoordinate p)
        (partialY smooth p))

  PolarDiskIntegralValue :
    (function : Point2 R -> R) ->
    (smooth : C2Data reals function) ->
    Point2 R ->
    R ->
    R ->
    Set
  PolarDiskIntegralValue function smooth center radius integralValue =
    Exists (R -> R)
      (\ radialIntegral ->
        ((angle : R) ->
          IntervalIntegralValue reals
            (zeroR reals)
            radius
            (\ radialCoordinate ->
              multiply reals
                (angularDensity function smooth
                  (addPoint reals center
                    (polarOffset radialCoordinate angle)))
                radialCoordinate)
            (radialIntegral angle))
        and
        IntervalIntegralValue reals
          (zeroR reals)
          twoPi
          radialIntegral
          integralValue)

  DistanceFromOrigin :
    Point2 R ->
    R ->
    Set
  DistanceFromOrigin center distance =
    lessOrEqual reals (zeroR reals) distance
    and
    squaredDistance reals center origin ==
      square reals distance

  Claim : Set
  Claim =
    (function : Point2 R -> R) ->
    (smooth : C2Data reals function) ->
    (d : R) ->
    StrictLess reals (zeroR reals) d ->
    (r : R) ->
    StrictLess reals (zeroR reals) r ->
    StrictLess reals r d ->
    Exists (Point2 R)
      (\ center ->
        DistanceFromOrigin center d
        and
        PolarDiskIntegralValue
          function
          smooth
          center
          r
          (zeroR reals))

  proposition : Set
  proposition =
    Iff Claim Top

putnam-2021-b3 : Set1
putnam-2021-b3 =
  (R : Set) ->
  (reals : CompleteOrderedRealField R) ->
  (trigonometry : StandardTrigonometry reals) ->
  Putnam2021B3Statement.proposition reals trigonometry
