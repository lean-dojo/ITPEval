-- Statement-only formalization of PutnamBench corpus artifact putnam_1980_a6:
-- the greatest universal lower bound, equal to 1 / exp(1), for the integral
-- of |f' - f| over [0,1] among C1 real functions with f(0)=0 and f(1)=1.
-- This file contains no proof.

{-# OPTIONS --safe #-}

open import Agda.Builtin.Equality renaming (_≡_ to _==_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)

infix 4 _!=_ _<=N_
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

data _<=N_ : Nat -> Nat -> Set where
  zero<=   : {n : Nat} -> zero <=N n
  suc<=suc : {m n : Nat} -> m <=N n -> suc m <=N suc n

record CompleteOrderedRealField (R : Set) : Set1 where
  field
    zeroR oneR : R
    add multiply : R -> R -> R
    negate inverse absoluteValue : R -> R
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

    absolute-nonnegative :
      (x : R) ->
      lessOrEqual zeroR (absoluteValue x)
    absolute-of-nonnegative :
      (x : R) ->
      lessOrEqual zeroR x ->
      absoluteValue x == x
    absolute-of-nonpositive :
      (x : R) ->
      lessOrEqual x zeroR ->
      absoluteValue x == negate x

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

Between :
  {R : Set} ->
  CompleteOrderedRealField R ->
  R ->
  R ->
  R ->
  Set
Between reals lower upper x =
  lessOrEqual reals lower x
  and
  lessOrEqual reals x upper

ContinuousOnInterval :
  {R : Set} ->
  CompleteOrderedRealField R ->
  R ->
  R ->
  (R -> R) ->
  Set
ContinuousOnInterval {R} reals lower upper function =
  (point : R) ->
  Between reals lower upper point ->
  (epsilon : R) ->
  StrictLess reals (zeroR reals) epsilon ->
  Exists R
    (\ delta ->
      StrictLess reals (zeroR reals) delta
      and
      ((x : R) ->
        Between reals lower upper x ->
        CloseTo reals point delta x ->
        CloseTo reals
          (function point)
          epsilon
          (function x)))

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

DerivativeWithinIntervalAt :
  {R : Set} ->
  CompleteOrderedRealField R ->
  R ->
  R ->
  (R -> R) ->
  R ->
  R ->
  Set
DerivativeWithinIntervalAt {R} reals lower upper function point derivative =
  (epsilon : R) ->
  StrictLess reals (zeroR reals) epsilon ->
  Exists R
    (\ delta ->
      StrictLess reals (zeroR reals) delta
      and
      ((x : R) ->
        Between reals lower upper x ->
        CloseTo reals point delta x ->
        x != point ->
        CloseTo reals derivative epsilon
          (differenceQuotient reals function point x)))

record C1UnitIntervalFunction
  {R : Set}
  (reals : CompleteOrderedRealField R)
  (function : R -> R) :
  Set where

  field
    derivative : R -> R

    function-continuous :
      ContinuousOnInterval reals
        (zeroR reals)
        (oneR reals)
        function

    derivative-correct :
      (x : R) ->
      Between reals (zeroR reals) (oneR reals) x ->
      DerivativeWithinIntervalAt reals
        (zeroR reals)
        (oneR reals)
        function
        x
        (derivative x)

    derivative-continuous :
      ContinuousOnInterval reals
        (zeroR reals)
        (oneR reals)
        derivative

    value-at-zero :
      function (zeroR reals) == zeroR reals

    value-at-one :
      function (oneR reals) == oneR reals

open C1UnitIntervalFunction

oneN : Nat
oneN =
  suc zero

factorial : Nat -> Nat
factorial zero =
  oneN
factorial (suc n) =
  suc n * factorial n

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

SeriesHasSum :
  {R : Set} ->
  CompleteOrderedRealField R ->
  (Nat -> R) ->
  R ->
  Set
SeriesHasSum reals terms limit =
  ConvergesTo reals
    (\ n -> sumFirst reals n terms)
    limit

exponentialTerm :
  {R : Set} ->
  CompleteOrderedRealField R ->
  R ->
  Nat ->
  R
exponentialTerm reals x n =
  divide reals
    (naturalPower reals x n)
    (fromNat reals (factorial n))

record StandardExponential
  {R : Set}
  (reals : CompleteOrderedRealField R) :
  Set1 where

  field
    exponential : R -> R

    exponential-series :
      (x : R) ->
      SeriesHasSum reals
        (exponentialTerm reals x)
        (exponential x)

    exponential-positive :
      (x : R) ->
      StrictLess reals
        (zeroR reals)
        (exponential x)

open StandardExponential

midpointRiemannSum :
  {R : Set} ->
  CompleteOrderedRealField R ->
  R ->
  R ->
  (R -> R) ->
  Nat ->
  R
midpointRiemannSum reals lower upper function pieces =
  let
    two =
      fromNat reals (suc (suc zero))
    step =
      divide reals
        (subtract reals upper lower)
        (fromNat reals pieces)
    halfStep =
      divide reals step two
  in
  sumFirst reals pieces
    (\ i ->
      multiply reals
        (function
          (add reals lower
            (add reals
              (multiply reals
                (fromNat reals i)
                step)
              halfStep)))
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
      midpointRiemannSum reals
        lower
        upper
        function
        (suc n))
    value

record StandardIntervalIntegration
  {R : Set}
  (reals : CompleteOrderedRealField R) :
  Set1 where

  field
    intervalIntegral :
      R ->
      R ->
      (R -> R) ->
      R

    integral-of-continuous :
      (lower upper : R) ->
      (function : R -> R) ->
      lessOrEqual reals lower upper ->
      ContinuousOnInterval reals lower upper function ->
      IntervalIntegralValue reals
        lower
        upper
        function
        (intervalIntegral lower upper function)

open StandardIntervalIntegration

record IsGreatest
  {R : Set}
  (reals : CompleteOrderedRealField R)
  (property : R -> Set)
  (greatest : R) :
  Set where

  field
    belongs :
      property greatest

    greatest-property :
      (x : R) ->
      property x ->
      lessOrEqual reals x greatest

module Putnam1980A6Statement
  {R : Set}
  (reals : CompleteOrderedRealField R)
  (analysis : StandardExponential reals)
  (integration : StandardIntervalIntegration reals) where

  solution : R
  solution =
    divide reals
      (oneR reals)
      (exponential analysis (oneR reals))

  integrand :
    (function : R -> R) ->
    C1UnitIntervalFunction reals function ->
    R ->
    R
  integrand function admissible x =
    absoluteValue reals
      (subtract reals
        (derivative admissible x)
        (function x))

  objective :
    (function : R -> R) ->
    C1UnitIntervalFunction reals function ->
    R
  objective function admissible =
    intervalIntegral integration
      (zeroR reals)
      (oneR reals)
      (integrand function admissible)

  UniversalLowerBound : R -> Set
  UniversalLowerBound lower =
    (function : R -> R) ->
    (admissible : C1UnitIntervalFunction reals function) ->
    lessOrEqual reals lower (objective function admissible)

  proposition : Set
  proposition =
    IsGreatest reals UniversalLowerBound solution

putnam-1980-a6 : Set1
putnam-1980-a6 =
  (R : Set) ->
  (reals : CompleteOrderedRealField R) ->
  (analysis : StandardExponential reals) ->
  (integration : StandardIntervalIntegration reals) ->
  Putnam1980A6Statement.proposition reals analysis integration
