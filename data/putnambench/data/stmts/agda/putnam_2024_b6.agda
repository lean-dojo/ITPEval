-- Statement-only formalization of PutnamBench corpus artifact putnam_2024_b6
-- (putnambench__agda__putnam_2024_b6): the threshold for the left-hand
-- asymptotics of a real exponential power series at x = 1 is c = -1/2.
-- This file contains no proof.

{-# OPTIONS --safe #-}

module Putnam2024B6 where

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

oneN : Nat
oneN =
  suc zero

twoN : Nat
twoN =
  suc oneN

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

InHalfOpenUnitInterval :
  {R : Set} ->
  CompleteOrderedRealField R ->
  R ->
  Set
InHalfOpenUnitInterval reals x =
  lessOrEqual reals (zeroR reals) x
  and
  StrictLess reals x (oneR reals)

CloseTo :
  {R : Set} ->
  CompleteOrderedRealField R ->
  R ->
  R ->
  R ->
  Set
CloseTo reals center radius x =
  StrictLess reals
    (absoluteValue reals (subtract reals x center))
    radius

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
ConvergesTo reals sequence limit =
  (epsilon : _) ->
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
SeriesHasSum reals terms value =
  ConvergesTo reals
    (\ n -> sumFirst reals n terms)
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

record StandardExponential
  {R : Set}
  (reals : CompleteOrderedRealField R) :
  Set1 where

  field
    exponential logarithm : R -> R

    exponential-is-power-series :
      (x : R) ->
      SeriesHasSum reals
        (exponentialTerm reals x)
        (exponential x)
    exponential-positive :
      (x : R) ->
      StrictLess reals (zeroR reals) (exponential x)
    logarithm-of-exponential :
      (x : R) ->
      logarithm (exponential x) == x
    exponential-of-logarithm :
      (x : R) ->
      StrictLess reals (zeroR reals) x ->
      exponential (logarithm x) == x

open StandardExponential

positiveRealPower :
  {R : Set} ->
  (reals : CompleteOrderedRealField R) ->
  StandardExponential reals ->
  R ->
  R ->
  R
positiveRealPower reals analysis base exponent =
  exponential analysis
    (multiply reals exponent (logarithm analysis base))

putnamTerm :
  {R : Set} ->
  (reals : CompleteOrderedRealField R) ->
  StandardExponential reals ->
  R ->
  R ->
  Nat ->
  R
putnamTerm reals analysis a x n =
  multiply reals
    (multiply reals
      (positiveRealPower reals analysis
        (fromNat reals (suc n))
        a)
      (exponential analysis
        (multiply reals
          (fromNat reals twoN)
          (fromNat reals (suc n)))))
    (naturalPower reals x ((suc n) * (suc n)))

SeriesDefinition :
  {R : Set} ->
  (reals : CompleteOrderedRealField R) ->
  StandardExponential reals ->
  (R -> R -> R) ->
  Set
SeriesDefinition {R} reals analysis F =
  (a x : R) ->
  InHalfOpenUnitInterval reals x ->
  SeriesHasSum reals
    (putnamTerm reals analysis a x)
    (F a x)

ApproachesOneFromLeft :
  {R : Set} ->
  CompleteOrderedRealField R ->
  R ->
  R ->
  Set
ApproachesOneFromLeft reals delta x =
  StrictLess reals
    (subtract reals (oneR reals) delta)
    x
  and
  StrictLess reals x (oneR reals)

LeftLimitZero :
  {R : Set} ->
  CompleteOrderedRealField R ->
  (R -> R) ->
  Set
LeftLimitZero {R} reals function =
  (epsilon : R) ->
  StrictLess reals (zeroR reals) epsilon ->
  Exists R
    (\ delta ->
      StrictLess reals (zeroR reals) delta
      and
      ((x : R) ->
        ApproachesOneFromLeft reals delta x ->
        StrictLess reals
          (absoluteValue reals (function x))
          epsilon))

LeftLimitAtTop :
  {R : Set} ->
  CompleteOrderedRealField R ->
  (R -> R) ->
  Set
LeftLimitAtTop {R} reals function =
  (bound : R) ->
  Exists R
    (\ delta ->
      StrictLess reals (zeroR reals) delta
      and
      ((x : R) ->
        ApproachesOneFromLeft reals delta x ->
        lessOrEqual reals bound (function x)))

normalizedValue :
  {R : Set} ->
  (reals : CompleteOrderedRealField R) ->
  StandardExponential reals ->
  (R -> R -> R) ->
  R ->
  R ->
  R
normalizedValue reals analysis F a x =
  multiply reals
    (F a x)
    (exponential analysis
      (negate reals
        (divide reals
          (oneR reals)
          (subtract reals (oneR reals) x))))

ThresholdProperty :
  {R : Set} ->
  (reals : CompleteOrderedRealField R) ->
  StandardExponential reals ->
  (R -> R -> R) ->
  R ->
  Set
ThresholdProperty {R} reals analysis F c =
  ((a : R) ->
    StrictLess reals a c ->
    LeftLimitZero reals
      (normalizedValue reals analysis F a))
  and
  ((a : R) ->
    StrictLess reals c a ->
    LeftLimitAtTop reals
      (normalizedValue reals analysis F a))

negativeHalf :
  {R : Set} ->
  CompleteOrderedRealField R ->
  R
negativeHalf reals =
  divide reals
    (negate reals (oneR reals))
    (fromNat reals twoN)

putnam-2024-b6 : Set1
putnam-2024-b6 =
  (R : Set) ->
  (reals : CompleteOrderedRealField R) ->
  (analysis : StandardExponential reals) ->
  (F : R -> R -> R) ->
  (c : R) ->
  SeriesDefinition reals analysis F ->
  Iff
    (ThresholdProperty reals analysis F c)
    (c == negativeHalf reals)
