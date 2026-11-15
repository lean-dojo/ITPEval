-- Statement-only formalization of PutnamBench corpus artifact putnam_1970_b1:
-- the limit of a normalized finite product of real powers is
-- exp(2 * log 5 - 4 + 2 * arctan 2). This file contains no proof.

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

record CompleteOrderedField (R : Set) : Set1 where
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

open CompleteOrderedField

oneN : Nat
oneN =
  suc zero

twoN : Nat
twoN =
  suc oneN

fourN : Nat
fourN =
  twoN + twoN

fiveN : Nat
fiveN =
  suc fourN

subtract :
  {R : Set} ->
  CompleteOrderedField R ->
  R ->
  R ->
  R
subtract reals x y =
  add reals x (negate reals y)

divide :
  {R : Set} ->
  CompleteOrderedField R ->
  R ->
  R ->
  R
divide reals x y =
  multiply reals x (inverse reals y)

StrictLess :
  {R : Set} ->
  CompleteOrderedField R ->
  R ->
  R ->
  Set
StrictLess reals x y =
  lessOrEqual reals x y and x != y

CloseTo :
  {R : Set} ->
  CompleteOrderedField R ->
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
  CompleteOrderedField R ->
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
  CompleteOrderedField R ->
  Nat ->
  (Nat -> R) ->
  R
sumFirst reals zero term =
  zeroR reals
sumFirst reals (suc n) term =
  add reals
    (sumFirst reals n term)
    (term n)

productFirst :
  {R : Set} ->
  CompleteOrderedField R ->
  Nat ->
  (Nat -> R) ->
  R
productFirst reals zero term =
  oneR reals
productFirst reals (suc n) term =
  multiply reals
    (productFirst reals n term)
    (term n)

ConvergesTo :
  {R : Set} ->
  CompleteOrderedField R ->
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
  CompleteOrderedField R ->
  (Nat -> R) ->
  R ->
  Set
SeriesHasSum reals terms limit =
  ConvergesTo reals
    (\ n -> sumFirst reals n terms)
    limit

exponentialTerm :
  {R : Set} ->
  CompleteOrderedField R ->
  R ->
  Nat ->
  R
exponentialTerm reals x n =
  divide reals
    (naturalPower reals x n)
    (fromNat reals (factorial n))

ExponentialValue :
  {R : Set} ->
  CompleteOrderedField R ->
  R ->
  R ->
  Set
ExponentialValue reals x value =
  SeriesHasSum reals
    (exponentialTerm reals x)
    value

record StandardRealPowers
  {R : Set}
  (reals : CompleteOrderedField R) :
  Set1 where

  field
    exponential logarithm : R -> R

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

open StandardRealPowers

realPower :
  {R : Set} ->
  {reals : CompleteOrderedField R} ->
  StandardRealPowers reals ->
  R ->
  R ->
  R
realPower {reals = reals} powers base exponent =
  exponential powers
    (multiply reals exponent (logarithm powers base))

rightRiemannSum :
  {R : Set} ->
  CompleteOrderedField R ->
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
  CompleteOrderedField R ->
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

arctangentIntegrand :
  {R : Set} ->
  CompleteOrderedField R ->
  R ->
  R
arctangentIntegrand reals x =
  inverse reals
    (add reals
      (oneR reals)
      (naturalPower reals x twoN))

record StandardRealAnalysis
  {R : Set}
  (reals : CompleteOrderedField R) :
  Set1 where

  field
    powers : StandardRealPowers reals
    arctangent : R -> R

    arctangent-integral :
      (x : R) ->
      lessOrEqual reals (zeroR reals) x ->
      IntervalIntegralValue reals
        (zeroR reals)
        x
        (arctangentIntegrand reals)
        (arctangent x)

open StandardRealAnalysis

module Putnam1970B1Statement
  {R : Set}
  (reals : CompleteOrderedField R)
  (analysis : StandardRealAnalysis reals) where

  realPowers : StandardRealPowers reals
  realPowers =
    powers analysis

  productFactor :
    Nat ->
    Nat ->
    R
  productFactor n i =
    realPower realPowers
      (add reals
        (naturalPower reals (fromNat reals n) twoN)
        (naturalPower reals (fromNat reals i) twoN))
      (divide reals
        (oneR reals)
        (fromNat reals n))

  normalizedProduct :
    Nat ->
    R
  normalizedProduct n =
    multiply reals
      (divide reals
        (oneR reals)
        (naturalPower reals
          (fromNat reals n)
          fourN))
      (productFirst reals
        (twoN * n)
        (\ i -> productFactor n (suc i)))

  solution : R
  solution =
    exponential realPowers
      (add reals
        (subtract reals
          (multiply reals
            (fromNat reals twoN)
            (logarithm realPowers
              (fromNat reals fiveN)))
          (fromNat reals fourN))
        (multiply reals
          (fromNat reals twoN)
          (arctangent analysis
            (fromNat reals twoN))))

  proposition : Set
  proposition =
    ConvergesTo reals
      normalizedProduct
      solution

putnam-1970-b1 : Set1
putnam-1970-b1 =
  (R : Set) ->
  (reals : CompleteOrderedField R) ->
  (analysis : StandardRealAnalysis reals) ->
  Putnam1970B1Statement.proposition reals analysis
