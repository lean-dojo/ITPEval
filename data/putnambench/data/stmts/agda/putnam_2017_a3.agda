-- Statement-only formalization of PutnamBench corpus artifact putnam_2017_a3
-- (putnambench__agda__putnam_2017_a3): distinct positive continuous real
-- functions with equal interval integrals define a strictly increasing integral
-- sequence tending to positive infinity. This file contains no proof.

{-# OPTIONS --safe #-}

module Putnam2017A3 where

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
      Exists Nat
        (\ n -> lessOrEqual x (fromNat n))
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

naturalPower :
  {R : Set} ->
  CompleteOrderedRealField R ->
  R ->
  Nat ->
  R
naturalPower reals x zero =
  oneR reals
naturalPower reals x (suc exponent) =
  multiply reals
    (naturalPower reals x exponent)
    x

StrictLess :
  {R : Set} ->
  CompleteOrderedRealField R ->
  R ->
  R ->
  Set
StrictLess reals x y =
  lessOrEqual reals x y and x != y

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
        CloseTo reals (function point) epsilon (function x)))

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

SequentialLimit :
  {R : Set} ->
  CompleteOrderedRealField R ->
  (Nat -> R) ->
  R ->
  Set
SequentialLimit reals sequence limit =
  (epsilon : _) ->
  StrictLess reals (zeroR reals) epsilon ->
  Exists Nat
    (\ cutoff ->
      (n : Nat) ->
      cutoff <=N n ->
      CloseTo reals limit epsilon (sequence n))

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

PositiveNat : Nat -> Set
PositiveNat n =
  suc zero <=N n

TendsToPositiveInfinity :
  {R : Set} ->
  CompleteOrderedRealField R ->
  (Nat -> R) ->
  Set
TendsToPositiveInfinity {R} reals sequence =
  (lower-bound : R) ->
  Exists Nat
    (\ cutoff ->
      (n : Nat) ->
      cutoff <=N n ->
      lessOrEqual reals lower-bound (sequence n))

module Putnam2017A3Statement
  {R : Set}
  (reals : CompleteOrderedRealField R) where

  integrand :
    (R -> R) ->
    (R -> R) ->
    Nat ->
    R ->
    R
  integrand f g n x =
    divide reals
      (naturalPower reals (f x) (suc n))
      (naturalPower reals (g x) n)

  EqualIntervalIntegrals :
    R ->
    R ->
    (R -> R) ->
    (R -> R) ->
    Set
  EqualIntervalIntegrals lower upper f g =
    Exists R
      (\ common-value ->
        IntervalIntegralValue reals lower upper f common-value
        and
        IntervalIntegralValue reals lower upper g common-value)

  DefinesIntegralSequence :
    R ->
    R ->
    (R -> R) ->
    (R -> R) ->
    (Nat -> R) ->
    Set
  DefinesIntegralSequence lower upper f g I =
    (n : Nat) ->
    PositiveNat n ->
    IntervalIntegralValue reals lower upper
      (integrand f g n)
      (I n)

  StrictlyIncreasingFromOne :
    (Nat -> R) ->
    Set
  StrictlyIncreasingFromOne I =
    (n : Nat) ->
    PositiveNat n ->
    StrictLess reals (I n) (I (suc n))

  proposition : Set
  proposition =
    (a b : R) ->
    (f g : R -> R) ->
    (I : Nat -> R) ->
    StrictLess reals a b ->
    ContinuousOnInterval reals a b f
    and
    ContinuousOnInterval reals a b g ->
    ((x : R) ->
      Between reals a b x ->
      StrictLess reals (zeroR reals) (f x))
    and
    ((x : R) ->
      Between reals a b x ->
      StrictLess reals (zeroR reals) (g x)) ->
    EqualIntervalIntegrals a b f g ->
    Exists R
      (\ x ->
        Between reals a b x
        and
        f x != g x) ->
    DefinesIntegralSequence a b f g I ->
    StrictlyIncreasingFromOne I
    and
    TendsToPositiveInfinity reals I

putnam-2017-a3 : Set1
putnam-2017-a3 =
  (R : Set) ->
  (reals : CompleteOrderedRealField R) ->
  Putnam2017A3Statement.proposition reals
