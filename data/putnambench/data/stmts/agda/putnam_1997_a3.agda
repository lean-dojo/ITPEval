-- Statement-only formalization of PutnamBench corpus artifact putnam_1997_a3:
-- the improper integral of the product of two specified real power series
-- equals the nonnegative square root of exp(1). This file contains no proof.

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

twoN : Nat
twoN =
  suc (suc zero)

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

evenFactor :
  {R : Set} ->
  CompleteOrderedRealField R ->
  Nat ->
  R
evenFactor reals zero =
  oneR reals
evenFactor reals (suc n) =
  multiply reals
    (fromNat reals (twoN * suc n))
    (evenFactor reals n)

evenFactorSquare :
  {R : Set} ->
  CompleteOrderedRealField R ->
  Nat ->
  R
evenFactorSquare reals zero =
  oneR reals
evenFactorSquare reals (suc n) =
  multiply reals
    (naturalPower reals
      (fromNat reals (twoN * suc n))
      twoN)
    (evenFactorSquare reals n)

firstSeriesTerm :
  {R : Set} ->
  CompleteOrderedRealField R ->
  R ->
  Nat ->
  R
firstSeriesTerm reals x n =
  divide reals
    (multiply reals
      (alternatingPower reals n)
      (naturalPower reals x (suc (twoN * n))))
    (evenFactor reals n)

secondSeriesTerm :
  {R : Set} ->
  CompleteOrderedRealField R ->
  R ->
  Nat ->
  R
secondSeriesTerm reals x n =
  divide reals
    (naturalPower reals x (twoN * n))
    (evenFactorSquare reals n)

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

record StandardRealAnalysis
  (R : Set) :
  Set1 where

  field
    algebra :
      CompleteOrderedRealField R
    exponential squareRoot :
      R -> R

    exponential-series :
      (x : R) ->
      SeriesHasSum algebra
        (exponentialTerm algebra x)
        (exponential x)
    exponential-positive :
      (x : R) ->
      StrictLess algebra
        (zeroR algebra)
        (exponential x)

    square-root-nonnegative :
      (x : R) ->
      lessOrEqual algebra (zeroR algebra) x ->
      lessOrEqual algebra
        (zeroR algebra)
        (squareRoot x)
    square-root-square :
      (x : R) ->
      lessOrEqual algebra (zeroR algebra) x ->
      multiply algebra
        (squareRoot x)
        (squareRoot x)
      ==
      x

open StandardRealAnalysis

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

ImproperIntegralValue :
  {R : Set} ->
  CompleteOrderedRealField R ->
  (R -> R) ->
  R ->
  Set
ImproperIntegralValue {R} reals function limit =
  (epsilon : R) ->
  StrictLess reals (zeroR reals) epsilon ->
  Exists R
    (\ threshold ->
      (upper : R) ->
      lessOrEqual reals threshold upper ->
      Exists R
        (\ integralValue ->
          IntervalIntegralValue reals
            (zeroR reals)
            upper
            function
            integralValue
          and
          CloseTo reals limit epsilon integralValue))

module Putnam1997A3Statement
  {R : Set}
  (analysis : StandardRealAnalysis R)
  (series1 series2 : R -> R) where

  reals : CompleteOrderedRealField R
  reals =
    algebra analysis

  integrand : R -> R
  integrand x =
    multiply reals
      (series1 x)
      (series2 x)

  solution : R
  solution =
    squareRoot analysis
      (exponential analysis (oneR reals))

  proposition : Set
  proposition =
    ((x : R) ->
      SeriesHasSum reals
        (firstSeriesTerm reals x)
        (series1 x))
    ->
    ((x : R) ->
      SeriesHasSum reals
        (secondSeriesTerm reals x)
        (series2 x))
    ->
    ImproperIntegralValue reals
      integrand
      solution

putnam-1997-a3 : Set1
putnam-1997-a3 =
  (R : Set) ->
  (analysis : StandardRealAnalysis R) ->
  (series1 series2 : R -> R) ->
  Putnam1997A3Statement.proposition
    analysis
    series1
    series2
