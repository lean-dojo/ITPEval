-- Statement-only formalization of PutnamBench corpus artifact putnam_1987_a3:
-- the two proposed positivity implications for solutions of
-- f'' - 2 f' + f = 2 exp(x) are respectively false and true.
-- This file contains no proof.

{-# OPTIONS --safe #-}

open import Agda.Builtin.Equality renaming (_≡_ to _==_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)

infix 4 _!=_ _<=N_
infixr 3 _and_
infixr 2 _or_

data Bottom : Set where

record Top : Set where
  constructor trivial

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

StrictLess :
  {R : Set} ->
  CompleteOrderedRealField R ->
  R ->
  R ->
  Set
StrictLess reals x y =
  lessOrEqual reals x y and x != y

Positive :
  {R : Set} ->
  CompleteOrderedRealField R ->
  R ->
  Set
Positive reals x =
  StrictLess reals (zeroR reals) x

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

partialSum :
  {R : Set} ->
  CompleteOrderedRealField R ->
  (Nat -> R) ->
  Nat ->
  R
partialSum reals terms zero =
  zeroR reals
partialSum reals terms (suc n) =
  add reals
    (partialSum reals terms n)
    (terms n)

ConvergesTo :
  {R : Set} ->
  CompleteOrderedRealField R ->
  (Nat -> R) ->
  R ->
  Set
ConvergesTo {R} reals sequence limit =
  (epsilon : R) ->
  Positive reals epsilon ->
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
SeriesHasSum reals terms value =
  ConvergesTo reals
    (partialSum reals terms)
    value

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

ExponentialValue :
  {R : Set} ->
  CompleteOrderedRealField R ->
  R ->
  R ->
  Set
ExponentialValue reals x value =
  SeriesHasSum reals
    (exponentialTerm reals x)
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
DerivativeAt {R} reals function point derivativeValue =
  (epsilon : R) ->
  Positive reals epsilon ->
  Exists R
    (\ delta ->
      Positive reals delta
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

record StandardExponential
  {R : Set}
  (reals : CompleteOrderedRealField R) : Set1 where

  field
    exponential : R -> R

    exponential-series :
      (x : R) ->
      ExponentialValue reals x (exponential x)

open StandardExponential

module Putnam1987A3Statement
  {R : Set}
  (reals : CompleteOrderedRealField R)
  (calculus : StandardRealCalculus reals)
  (analysis : StandardExponential reals) where

  firstDerivative : (R -> R) -> R -> R
  firstDerivative function =
    derivative calculus function

  secondDerivative : (R -> R) -> R -> R
  secondDerivative function =
    derivative calculus (firstDerivative function)

  TwiceDifferentiableAt : (R -> R) -> R -> Set
  TwiceDifferentiableAt function x =
    HasDerivativeAt reals function x
    and
    HasDerivativeAt reals (firstDerivative function) x

  SatisfiesEquationAt : (R -> R) -> R -> Set
  SatisfiesEquationAt function x =
    add reals
      (subtract reals
        (secondDerivative function x)
        (multiply reals
          (fromNat reals twoN)
          (firstDerivative function x)))
      (function x)
    ==
    multiply reals
      (fromNat reals twoN)
      (exponential analysis x)

  PositiveFunctionHypothesis : (R -> R) -> Set
  PositiveFunctionHypothesis function =
    (x : R) ->
    TwiceDifferentiableAt function x
    and
    SatisfiesEquationAt function x
    and
    Positive reals (function x)

  PositiveDerivativeHypothesis : (R -> R) -> Set
  PositiveDerivativeHypothesis function =
    (x : R) ->
    TwiceDifferentiableAt function x
    and
    SatisfiesEquationAt function x
    and
    Positive reals (firstDerivative function x)

  PositiveFunctionsHavePositiveDerivative : Set
  PositiveFunctionsHavePositiveDerivative =
    (function : R -> R) ->
    PositiveFunctionHypothesis function ->
    (x : R) ->
    Positive reals (firstDerivative function x)

  PositiveDerivativesGivePositiveFunction : Set
  PositiveDerivativesGivePositiveFunction =
    (function : R -> R) ->
    PositiveDerivativeHypothesis function ->
    (x : R) ->
    Positive reals (function x)

  proposition : Set
  proposition =
    Iff PositiveFunctionsHavePositiveDerivative Bottom
    and
    Iff PositiveDerivativesGivePositiveFunction Top

putnam-1987-a3 : Set1
putnam-1987-a3 =
  (R : Set) ->
  (reals : CompleteOrderedRealField R) ->
  (calculus : StandardRealCalculus reals) ->
  (analysis : StandardExponential reals) ->
  Putnam1987A3Statement.proposition reals calculus analysis
