-- Statement-only formalization of PutnamBench corpus artifact putnam_1979_b2:
-- the punctured limit at zero of a real power of an integral over [0, 1],
-- with its closed form in terms of two positive real parameters.
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

SequentialLimit :
  {R : Set} ->
  CompleteOrderedRealField R ->
  (Nat -> R) ->
  R ->
  Set
SequentialLimit {R} reals sequence limit =
  (epsilon : R) ->
  StrictLess reals (zeroR reals) epsilon ->
  Exists Nat
    (\ cutoff ->
      (n : Nat) ->
      cutoff <=N n ->
      CloseTo reals limit epsilon (sequence n))

LimitAt :
  {R : Set} ->
  CompleteOrderedRealField R ->
  (R -> R) ->
  R ->
  R ->
  Set
LimitAt {R} reals function limit point =
  (epsilon : R) ->
  StrictLess reals (zeroR reals) epsilon ->
  Exists R
    (\ delta ->
      StrictLess reals (zeroR reals) delta
      and
      ((x : R) ->
        CloseTo reals point delta x ->
        x != point ->
        CloseTo reals limit epsilon (function x)))

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
  suc zero
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

exponentialPartialSum :
  {R : Set} ->
  CompleteOrderedRealField R ->
  R ->
  Nat ->
  R
exponentialPartialSum reals x terms =
  sumFirst reals terms
    (\ n ->
      divide reals
        (naturalPower reals x n)
        (fromNat reals (factorial n)))

ExponentialValue :
  {R : Set} ->
  CompleteOrderedRealField R ->
  R ->
  R ->
  Set
ExponentialValue reals x value =
  SequentialLimit reals
    (exponentialPartialSum reals x)
    value

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
  SequentialLimit reals
    (\ n ->
      rightRiemannSum reals
        lower
        upper
        function
        (suc n))
    value

record StandardRealAnalysis
  {R : Set}
  (reals : CompleteOrderedRealField R) :
  Set1 where

  field
    exponential naturalLogarithm : R -> R

    exponential-is-power-series :
      (x : R) ->
      ExponentialValue reals x (exponential x)

    exponential-positive :
      (x : R) ->
      StrictLess reals
        (zeroR reals)
        (exponential x)

    logarithm-of-exponential :
      (x : R) ->
      naturalLogarithm (exponential x) == x

    exponential-of-logarithm :
      (x : R) ->
      StrictLess reals (zeroR reals) x ->
      exponential (naturalLogarithm x) == x

    intervalIntegral :
      R ->
      R ->
      (R -> R) ->
      R

    interval-integral-is-riemann :
      (lower upper : R) ->
      (function : R -> R) ->
      Exists R
        (\ value ->
          IntervalIntegralValue reals
            lower
            upper
            function
            value) ->
      IntervalIntegralValue reals
        lower
        upper
        function
        (intervalIntegral lower upper function)

open StandardRealAnalysis

realPower :
  {R : Set} ->
  (reals : CompleteOrderedRealField R) ->
  StandardRealAnalysis reals ->
  R ->
  R ->
  R
realPower reals analysis base exponent =
  exponential analysis
    (multiply reals
      exponent
      (naturalLogarithm analysis base))

module Putnam1979B2Statement
  {R : Set}
  (reals : CompleteOrderedRealField R)
  (analysis : StandardRealAnalysis reals) where

  affineValue : R -> R -> R -> R
  affineValue a b x =
    add reals
      (multiply reals b x)
      (multiply reals a
        (subtract reals (oneR reals) x))

  integrand : R -> R -> R -> R -> R
  integrand a b t x =
    realPower reals analysis
      (affineValue a b x)
      t

  integralValue : R -> R -> R -> R
  integralValue a b t =
    intervalIntegral analysis
      (zeroR reals)
      (oneR reals)
      (integrand a b t)

  limitExpression : R -> R -> R -> R
  limitExpression a b t =
    realPower reals analysis
      (integralValue a b t)
      (inverse reals t)

  solution : R -> R -> R
  solution a b =
    divide reals
      (exponential analysis
        (multiply reals
          (divide reals b (subtract reals b a))
          (naturalLogarithm analysis b)))
      (multiply reals
        (exponential analysis (oneR reals))
        (exponential analysis
          (multiply reals
            (divide reals a (subtract reals b a))
            (naturalLogarithm analysis a))))

  proposition : Set
  proposition =
    (a b : R) ->
    StrictLess reals (zeroR reals) a ->
    StrictLess reals a b ->
    LimitAt reals
      (limitExpression a b)
      (solution a b)
      (zeroR reals)

putnam-1979-b2 : Set1
putnam-1979-b2 =
  (R : Set) ->
  (reals : CompleteOrderedRealField R) ->
  (analysis : StandardRealAnalysis reals) ->
  Putnam1979B2Statement.proposition reals analysis
