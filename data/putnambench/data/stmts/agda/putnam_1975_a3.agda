-- Statement-only formalization of PutnamBench corpus artifact putnam_1975_a3:
-- the explicit maximum and minimum points of a real-power objective on a
-- nonnegative real-power constraint surface. This file contains no proof.

{-# OPTIONS --safe #-}

module Putnam1975A3 where

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

record StandardNonnegativeRealPowers
  {R : Set}
  (reals : CompleteOrderedRealField R) :
  Set1 where

  field
    exponential logarithm : R -> R
    realPower : R -> R -> R

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

    positive-base-power :
      (base exponent : R) ->
      StrictLess reals (zeroR reals) base ->
      realPower base exponent ==
      exponential
        (multiply reals exponent (logarithm base))

    zero-positive-power :
      (exponent : R) ->
      StrictLess reals (zeroR reals) exponent ->
      realPower (zeroR reals) exponent == zeroR reals

open StandardNonnegativeRealPowers

record Triple (R : Set) : Set where
  constructor triple
  field
    firstCoordinate  : R
    secondCoordinate : R
    thirdCoordinate  : R

open Triple

module Putnam1975A3Statement
  {R : Set}
  (reals : CompleteOrderedRealField R)
  (powers : StandardNonnegativeRealPowers reals) where

  powerSum : R -> Triple R -> R
  powerSum exponent point =
    add reals
      (add reals
        (realPower powers (firstCoordinate point) exponent)
        (realPower powers (secondCoordinate point) exponent))
      (realPower powers (thirdCoordinate point) exponent)

  Feasible : R -> Triple R -> Set
  Feasible exponent point =
    lessOrEqual reals (zeroR reals) (firstCoordinate point)
    and
    lessOrEqual reals (zeroR reals) (secondCoordinate point)
    and
    lessOrEqual reals (zeroR reals) (thirdCoordinate point)
    and
    powerSum exponent point == oneR reals

  objective : R -> R -> R -> Triple R -> R
  objective a b c point =
    add reals
      (add reals
        (realPower powers (firstCoordinate point) a)
        (realPower powers (secondCoordinate point) b))
      (realPower powers (thirdCoordinate point) c)

  maximumFirstCoordinate : R -> R -> R
  maximumFirstCoordinate a b =
    realPower powers
      (divide reals a b)
      (divide reals
        (oneR reals)
        (subtract reals b a))

  maximumSecondCoordinate : R -> R -> R
  maximumSecondCoordinate a b =
    realPower powers
      (subtract reals
        (oneR reals)
        (realPower powers
          (maximumFirstCoordinate a b)
          b))
      (divide reals (oneR reals) b)

  maximumPoint : R -> R -> R -> Triple R
  maximumPoint a b c =
    triple
      (maximumFirstCoordinate a b)
      (maximumSecondCoordinate a b)
      (zeroR reals)

  minimumThirdCoordinate : R -> R -> R
  minimumThirdCoordinate b c =
    realPower powers
      (divide reals b c)
      (divide reals
        (oneR reals)
        (subtract reals c b))

  minimumSecondCoordinate : R -> R -> R
  minimumSecondCoordinate b c =
    realPower powers
      (subtract reals
        (oneR reals)
        (realPower powers
          (minimumThirdCoordinate b c)
          b))
      (divide reals (oneR reals) b)

  minimumPoint : R -> R -> R -> Triple R
  minimumPoint a b c =
    triple
      (zeroR reals)
      (minimumSecondCoordinate b c)
      (minimumThirdCoordinate b c)

  IsMaximumPoint : R -> R -> R -> Triple R -> Set
  IsMaximumPoint a b c candidate =
    Feasible b candidate
    and
    ((point : Triple R) ->
      Feasible b point ->
      lessOrEqual reals
        (objective a b c point)
        (objective a b c candidate))

  IsMinimumPoint : R -> R -> R -> Triple R -> Set
  IsMinimumPoint a b c candidate =
    Feasible b candidate
    and
    ((point : Triple R) ->
      Feasible b point ->
      lessOrEqual reals
        (objective a b c candidate)
        (objective a b c point))

  proposition : Set
  proposition =
    (a b c : R) ->
    StrictLess reals (zeroR reals) a ->
    StrictLess reals a b ->
    StrictLess reals b c ->
    IsMaximumPoint a b c (maximumPoint a b c)
    and
    IsMinimumPoint a b c (minimumPoint a b c)

putnam-1975-a3 : Set1
putnam-1975-a3 =
  (R : Set) ->
  (reals : CompleteOrderedRealField R) ->
  (powers : StandardNonnegativeRealPowers reals) ->
  Putnam1975A3Statement.proposition reals powers
