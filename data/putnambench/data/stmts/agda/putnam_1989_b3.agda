-- Statement-only formalization of PutnamBench corpus artifact putnam_1989_b3:
-- the moment formula and normalized-moment convergence for a differentiable
-- real function satisfying a dilation differential equation and decay bound.
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

oneN : Nat
oneN =
  suc zero

twoN : Nat
twoN =
  suc oneN

threeN : Nat
threeN =
  suc twoN

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

maximum :
  {R : Set} ->
  CompleteOrderedRealField R ->
  R ->
  R ->
  R
maximum reals x y with order-total reals x y
... | left _ =
  y
... | right _ =
  x

absoluteValue :
  {R : Set} ->
  CompleteOrderedRealField R ->
  R ->
  R
absoluteValue reals x =
  maximum reals x (negate reals x)

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

record StandardExponentialAndSquareRoot
  {R : Set}
  (reals : CompleteOrderedRealField R) :
  Set1 where

  field
    exponential squareRoot : R -> R

    exponential-series :
      (x : R) ->
      SeriesHasSum reals
        (exponentialTerm reals x)
        (exponential x)

    square-root-nonnegative :
      (x : R) ->
      lessOrEqual reals (zeroR reals) x ->
      lessOrEqual reals (zeroR reals) (squareRoot x)
    square-root-square :
      (x : R) ->
      lessOrEqual reals (zeroR reals) x ->
      multiply reals (squareRoot x) (squareRoot x) == x
    square-root-unique :
      (x y : R) ->
      lessOrEqual reals (zeroR reals) x ->
      lessOrEqual reals (zeroR reals) y ->
      multiply reals y y == x ->
      y == squareRoot x

open StandardExponentialAndSquareRoot

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

DerivativeWithinNonnegativeAt :
  {R : Set} ->
  CompleteOrderedRealField R ->
  (R -> R) ->
  R ->
  R ->
  Set
DerivativeWithinNonnegativeAt
  {R} reals function point derivativeValue =
  (epsilon : R) ->
  StrictLess reals (zeroR reals) epsilon ->
  Exists R
    (\ delta ->
      StrictLess reals (zeroR reals) delta
      and
      ((x : R) ->
        lessOrEqual reals (zeroR reals) x ->
        CloseTo reals point delta x ->
        x != point ->
        CloseTo reals derivativeValue epsilon
          (differenceQuotient reals function point x)))

DifferentiableOnNonnegative :
  {R : Set} ->
  CompleteOrderedRealField R ->
  (R -> R) ->
  Set
DifferentiableOnNonnegative {R} reals function =
  (x : R) ->
  lessOrEqual reals (zeroR reals) x ->
  Exists R
    (\ derivativeValue ->
      DerivativeWithinNonnegativeAt
        reals function x derivativeValue)

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

NonnegativeImproperIntegralValue :
  {R : Set} ->
  CompleteOrderedRealField R ->
  (R -> R) ->
  R ->
  Set
NonnegativeImproperIntegralValue {R} reals function value =
  Exists (Nat -> R)
    (\ partialIntegrals ->
      ((n : Nat) ->
        IntervalIntegralValue reals
          (zeroR reals)
          (fromNat reals n)
          function
          (partialIntegrals n))
      and
      ConvergesTo reals partialIntegrals value)

record StandardNonnegativeImproperIntegration
  {R : Set}
  (reals : CompleteOrderedRealField R) :
  Set1 where

  field
    improperIntegral :
      (R -> R) ->
      R

    integral-correct :
      (function : R -> R) ->
      (value : R) ->
      NonnegativeImproperIntegralValue reals function value ->
      improperIntegral function == value

    integral-totalized-at-zero :
      (function : R -> R) ->
      Not
        (Exists R
          (NonnegativeImproperIntegralValue reals function)) ->
      improperIntegral function == zeroR reals

open StandardNonnegativeImproperIntegration

factorProduct :
  {R : Set} ->
  CompleteOrderedRealField R ->
  Nat ->
  R
factorProduct reals zero =
  oneR reals
factorProduct reals (suc n) =
  multiply reals
    (factorProduct reals n)
    (subtract reals
      (oneR reals)
      (inverse reals
        (naturalPower reals
          (fromNat reals twoN)
          (suc n))))

momentSolution :
  {R : Set} ->
  CompleteOrderedRealField R ->
  Nat ->
  R ->
  R
momentSolution reals n initialMoment =
  divide reals
    (multiply reals
      initialMoment
      (fromNat reals (factorial n)))
    (multiply reals
      (naturalPower reals (fromNat reals threeN) n)
      (factorProduct reals n))

momentIntegrand :
  {R : Set} ->
  CompleteOrderedRealField R ->
  (R -> R) ->
  Nat ->
  R ->
  R
momentIntegrand reals function n x =
  multiply reals
    (naturalPower reals x n)
    (function x)

normalizedMoment :
  {R : Set} ->
  CompleteOrderedRealField R ->
  (Nat -> R) ->
  Nat ->
  R
normalizedMoment reals moments n =
  divide reals
    (multiply reals
      (moments n)
      (naturalPower reals (fromNat reals threeN) n))
    (fromNat reals (factorial n))

module Putnam1989B3Statement
  {R : Set}
  (reals : CompleteOrderedRealField R)
  (analysis : StandardExponentialAndSquareRoot reals)
  (integration : StandardNonnegativeImproperIntegration reals) where

  differentialEquation :
    (R -> R) ->
    Set
  differentialEquation function =
    (x : R) ->
    StrictLess reals (zeroR reals) x ->
    DerivativeWithinNonnegativeAt reals function x
      (add reals
        (negate reals
          (multiply reals
            (fromNat reals threeN)
            (function x)))
        (multiply reals
          (fromNat reals (threeN + threeN))
          (function
            (multiply reals
              (fromNat reals twoN)
              x))))

  decayBound :
    (R -> R) ->
    Set
  decayBound function =
    (x : R) ->
    lessOrEqual reals (zeroR reals) x ->
    lessOrEqual reals
      (absoluteValue reals (function x))
      (exponential analysis
        (negate reals (squareRoot analysis x)))

  momentsDefined :
    (R -> R) ->
    (Nat -> R) ->
    Set
  momentsDefined function moments =
    (n : Nat) ->
    moments n ==
    improperIntegral integration
      (momentIntegrand reals function n)

  conclusion :
    (Nat -> R) ->
    Set
  conclusion moments =
    ((n : Nat) ->
      moments n ==
      momentSolution reals n (moments zero))
    and
    Exists R
      (\ limit ->
        ConvergesTo reals
          (normalizedMoment reals moments)
          limit)
    and
    (ConvergesTo reals
      (normalizedMoment reals moments)
      (zeroR reals) ->
      moments zero == zeroR reals)

  proposition : Set
  proposition =
    (function : R -> R) ->
    DifferentiableOnNonnegative reals function ->
    differentialEquation function ->
    decayBound function ->
    (moments : Nat -> R) ->
    momentsDefined function moments ->
    conclusion moments

putnam-1989-b3 : Set1
putnam-1989-b3 =
  (R : Set) ->
  (reals : CompleteOrderedRealField R) ->
  (analysis : StandardExponentialAndSquareRoot reals) ->
  (integration : StandardNonnegativeImproperIntegration reals) ->
  Putnam1989B3Statement.proposition
    reals
    analysis
    integration
