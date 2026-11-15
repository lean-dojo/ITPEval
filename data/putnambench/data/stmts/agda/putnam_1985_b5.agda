-- Statement-only formalization of PutnamBench corpus artifact putnam_1985_b5:
-- assuming the Gaussian integral over the real line is sqrt pi, the improper
-- integral from zero to infinity of t^(-1/2) exp(-1985(t + t^(-1))) has the
-- value sqrt(pi / 1985) exp(-3970). This file contains no proof.

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

fourN : Nat
fourN =
  twoN + twoN

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
sumFirst reals zero term =
  zeroR reals
sumFirst reals (suc n) term =
  add reals
    (sumFirst reals n term)
    (term n)

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

alternatingPower :
  {R : Set} ->
  CompleteOrderedRealField R ->
  Nat ->
  R
alternatingPower reals n =
  naturalPower reals
    (negate reals (oneR reals))
    n

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

leibnizTerm :
  {R : Set} ->
  CompleteOrderedRealField R ->
  Nat ->
  R
leibnizTerm reals n =
  divide reals
    (alternatingPower reals n)
    (fromNat reals (suc (twoN * n)))

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

record PiValue
  {R : Set}
  (reals : CompleteOrderedRealField R)
  (value : R) : Set where
  field
    positive :
      StrictLess reals (zeroR reals) value
    leibniz-series :
      SeriesHasSum reals
        (leibnizTerm reals)
        (divide reals value (fromNat reals fourN))

record StandardRealAnalysis
  {R : Set}
  (reals : CompleteOrderedRealField R) : Set1 where
  field
    exponential logarithm squareRoot : R -> R
    pi : R

    exponential-series :
      (x : R) ->
      ExponentialValue reals x (exponential x)
    exponential-positive :
      (x : R) ->
      StrictLess reals
        (zeroR reals)
        (exponential x)
    exponential-injective :
      (x y : R) ->
      exponential x == exponential y ->
      x == y
    exponential-logarithm :
      (x : R) ->
      StrictLess reals (zeroR reals) x ->
      exponential (logarithm x) == x

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

    pi-value :
      PiValue reals pi

open StandardRealAnalysis

realPower :
  {R : Set} ->
  {reals : CompleteOrderedRealField R} ->
  StandardRealAnalysis reals ->
  R ->
  R ->
  R
realPower {reals = reals} analysis base exponent =
  exponential analysis
    (multiply reals
      exponent
      (logarithm analysis base))

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
    step =
      divide reals
        (subtract reals upper lower)
        (fromNat reals pieces)
    halfStep =
      divide reals
        step
        (fromNat reals twoN)
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

FiniteIntervalIntegralValue :
  {R : Set} ->
  CompleteOrderedRealField R ->
  R ->
  R ->
  (R -> R) ->
  R ->
  Set
FiniteIntervalIntegralValue reals lower upper function value =
  ConvergesTo reals
    (\ n ->
      midpointRiemannSum reals
        lower
        upper
        function
        (suc n))
    value

positiveCutoffIntegral :
  {R : Set} ->
  CompleteOrderedRealField R ->
  (R -> R) ->
  Nat ->
  Nat ->
  R
positiveCutoffIntegral reals function cutoff pieces =
  midpointRiemannSum reals
    (zeroR reals)
    (fromNat reals cutoff)
    function
    (suc pieces)

PositiveImproperIntegralValue :
  {R : Set} ->
  CompleteOrderedRealField R ->
  (R -> R) ->
  R ->
  Set
PositiveImproperIntegralValue reals function value =
  ConvergesTo reals
    (\ cutoff ->
      midpointRiemannSum reals
        (zeroR reals)
        (fromNat reals cutoff)
        function
        (suc (cutoff * cutoff)))
    value

WholeLineIntegralValue :
  {R : Set} ->
  CompleteOrderedRealField R ->
  (R -> R) ->
  R ->
  Set
WholeLineIntegralValue reals function value =
  ConvergesTo reals
    (\ cutoff ->
      midpointRiemannSum reals
        (negate reals (fromNat reals cutoff))
        (fromNat reals cutoff)
        function
        (suc (cutoff * cutoff)))
    value

module Putnam1985B5Statement
  {R : Set}
  (reals : CompleteOrderedRealField R)
  (analysis : StandardRealAnalysis reals) where

  fiveN : Nat
  fiveN =
    suc fourN

  tenN : Nat
  tenN =
    fiveN + fiveN

  nineteenN : Nat
  nineteenN =
    tenN + (fourN + fiveN)

  eightyFiveN : Nat
  eightyFiveN =
    (fourN * (tenN + tenN)) + fiveN

  oneThousandN : Nat
  oneThousandN =
    tenN * tenN * tenN

  nineteenHundredN : Nat
  nineteenHundredN =
    nineteenN * (tenN * tenN)

  nineteenEightyFiveN : Nat
  nineteenEightyFiveN =
    nineteenHundredN + eightyFiveN

  threeThousandNineHundredSeventyN : Nat
  threeThousandNineHundredSeventyN =
    nineteenEightyFiveN + nineteenEightyFiveN

  minusOneHalf : R
  minusOneHalf =
    negate reals
      (divide reals
        (oneR reals)
        (fromNat reals twoN))

  gaussian : R -> R
  gaussian x =
    exponential analysis
      (negate reals (square reals x))

  integrand : R -> R
  integrand t =
    multiply reals
      (realPower analysis t minusOneHalf)
      (exponential analysis
        (negate reals
          (multiply reals
            (fromNat reals nineteenEightyFiveN)
            (add reals t (inverse reals t)))))

  gaussianValue : R
  gaussianValue =
    squareRoot analysis (pi analysis)

  solution : R
  solution =
    multiply reals
      (squareRoot analysis
        (divide reals
          (pi analysis)
          (fromNat reals nineteenEightyFiveN)))
      (exponential analysis
        (negate reals
          (fromNat reals threeThousandNineHundredSeventyN)))

  proposition : Set
  proposition =
    WholeLineIntegralValue reals gaussian gaussianValue ->
    PositiveImproperIntegralValue reals integrand solution

putnam-1985-b5 : Set1
putnam-1985-b5 =
  (R : Set) ->
  (reals : CompleteOrderedRealField R) ->
  (analysis : StandardRealAnalysis reals) ->
  Putnam1985B5Statement.proposition reals analysis
