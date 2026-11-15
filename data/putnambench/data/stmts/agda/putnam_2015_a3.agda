-- Statement-only formalization of PutnamBench corpus artifact putnam_2015_a3
-- (putnambench__agda__putnam_2015_a3): the base-2 complex logarithm of a
-- 2015-by-2015 product of exponential factors is 13725. This file contains no proof.

{-# OPTIONS --safe #-}

module Putnam2015A3 where

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

alternatingSign :
  {R : Set} ->
  CompleteOrderedRealField R ->
  Nat ->
  R
alternatingSign reals zero =
  oneR reals
alternatingSign reals (suc n) =
  negate reals (alternatingSign reals n)

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

cosineTerm :
  {R : Set} ->
  CompleteOrderedRealField R ->
  R ->
  Nat ->
  R
cosineTerm reals x n =
  multiply reals
    (alternatingSign reals n)
    (divide reals
      (naturalPower reals x (twoN * n))
      (fromNat reals (factorial (twoN * n))))

sineTerm :
  {R : Set} ->
  CompleteOrderedRealField R ->
  R ->
  Nat ->
  R
sineTerm reals x n =
  multiply reals
    (alternatingSign reals n)
    (divide reals
      (naturalPower reals x (suc (twoN * n)))
      (fromNat reals (factorial (suc (twoN * n)))))

ExponentialValue :
  {R : Set} ->
  CompleteOrderedRealField R ->
  R ->
  R ->
  Set
ExponentialValue reals x value =
  SequentialLimit reals
    (\ n ->
      sumFirst reals n
        (exponentialTerm reals x))
    value

CosineValue :
  {R : Set} ->
  CompleteOrderedRealField R ->
  R ->
  R ->
  Set
CosineValue reals x value =
  SequentialLimit reals
    (\ n ->
      sumFirst reals n
        (cosineTerm reals x))
    value

SineValue :
  {R : Set} ->
  CompleteOrderedRealField R ->
  R ->
  R ->
  Set
SineValue reals x value =
  SequentialLimit reals
    (\ n ->
      sumFirst reals n
        (sineTerm reals x))
    value

record StandardRealAnalysis
  {R : Set}
  (reals : CompleteOrderedRealField R) :
  Set1 where

  field
    exponential naturalLogarithm cosine sine : R -> R
    pi : R

    exponential-is-power-series :
      (x : R) ->
      ExponentialValue reals x (exponential x)

    cosine-is-power-series :
      (x : R) ->
      CosineValue reals x (cosine x)

    sine-is-power-series :
      (x : R) ->
      SineValue reals x (sine x)

    exponential-positive :
      (x : R) ->
      StrictLess reals
        (zeroR reals)
        (exponential x)

    logarithm-zero :
      naturalLogarithm (zeroR reals) == zeroR reals

    logarithm-of-exponential :
      (x : R) ->
      naturalLogarithm (exponential x) == x

    exponential-of-logarithm :
      (x : R) ->
      StrictLess reals (zeroR reals) x ->
      exponential (naturalLogarithm x) == x

    pi-positive :
      StrictLess reals (zeroR reals) pi

    sine-pi :
      sine pi == zeroR reals

    pi-is-least-positive-sine-zero :
      (x : R) ->
      StrictLess reals (zeroR reals) x ->
      StrictLess reals x pi ->
      sine x != zeroR reals

open StandardRealAnalysis

record Complex (R : Set) : Set where
  constructor complex
  field
    realPart      : R
    imaginaryPart : R

open Complex

complexZero :
  {R : Set} ->
  CompleteOrderedRealField R ->
  Complex R
complexZero reals =
  complex (zeroR reals) (zeroR reals)

complexOne :
  {R : Set} ->
  CompleteOrderedRealField R ->
  Complex R
complexOne reals =
  complex (oneR reals) (zeroR reals)

complexFromReal :
  {R : Set} ->
  CompleteOrderedRealField R ->
  R ->
  Complex R
complexFromReal reals x =
  complex x (zeroR reals)

complexAdd :
  {R : Set} ->
  CompleteOrderedRealField R ->
  Complex R ->
  Complex R ->
  Complex R
complexAdd reals z w =
  complex
    (add reals (realPart z) (realPart w))
    (add reals (imaginaryPart z) (imaginaryPart w))

complexMultiply :
  {R : Set} ->
  CompleteOrderedRealField R ->
  Complex R ->
  Complex R ->
  Complex R
complexMultiply reals z w =
  complex
    (subtract reals
      (multiply reals (realPart z) (realPart w))
      (multiply reals (imaginaryPart z) (imaginaryPart w)))
    (add reals
      (multiply reals (realPart z) (imaginaryPart w))
      (multiply reals (imaginaryPart z) (realPart w)))

complexNormSquared :
  {R : Set} ->
  CompleteOrderedRealField R ->
  Complex R ->
  R
complexNormSquared reals z =
  add reals
    (multiply reals (realPart z) (realPart z))
    (multiply reals (imaginaryPart z) (imaginaryPart z))

complexInverse :
  {R : Set} ->
  CompleteOrderedRealField R ->
  Complex R ->
  Complex R
complexInverse reals z =
  let
    denominator =
      complexNormSquared reals z
  in
  complex
    (divide reals (realPart z) denominator)
    (negate reals
      (divide reals (imaginaryPart z) denominator))

complexDivide :
  {R : Set} ->
  CompleteOrderedRealField R ->
  Complex R ->
  Complex R ->
  Complex R
complexDivide reals z w =
  complexMultiply reals z (complexInverse reals w)

complexExponential :
  {R : Set} ->
  (reals : CompleteOrderedRealField R) ->
  StandardRealAnalysis reals ->
  Complex R ->
  Complex R
complexExponential reals analysis z =
  complex
    (multiply reals
      (exponential analysis (realPart z))
      (cosine analysis (imaginaryPart z)))
    (multiply reals
      (exponential analysis (realPart z))
      (sine analysis (imaginaryPart z)))

PrincipalArgumentValue :
  {R : Set} ->
  (reals : CompleteOrderedRealField R) ->
  StandardRealAnalysis reals ->
  Complex R ->
  R ->
  Set
PrincipalArgumentValue {R} reals analysis z theta =
  ((z == complexZero reals)
    and
    (theta == zeroR reals))
  or
  ((z != complexZero reals)
    and
    StrictLess reals
      (negate reals (pi analysis))
      theta
    and
    lessOrEqual reals theta (pi analysis)
    and
    Exists R
      (\ radius ->
        StrictLess reals (zeroR reals) radius
        and
        z ==
          complex
            (multiply reals radius (cosine analysis theta))
            (multiply reals radius (sine analysis theta))))

record StandardComplexAnalysis
  {R : Set}
  (reals : CompleteOrderedRealField R)
  (analysis : StandardRealAnalysis reals) :
  Set1 where

  field
    argument : Complex R -> R

    argument-is-principal :
      (z : Complex R) ->
      PrincipalArgumentValue reals analysis z (argument z)

open StandardComplexAnalysis

complexLogarithm :
  {R : Set} ->
  (reals : CompleteOrderedRealField R) ->
  (analysis : StandardRealAnalysis reals) ->
  StandardComplexAnalysis reals analysis ->
  Complex R ->
  Complex R
complexLogarithm reals analysis complexAnalysis z =
  complex
    (divide reals
      (naturalLogarithm analysis
        (complexNormSquared reals z))
      (fromNat reals twoN))
    (argument complexAnalysis z)

complexProductFirst :
  {R : Set} ->
  CompleteOrderedRealField R ->
  Nat ->
  (Nat -> Complex R) ->
  Complex R
complexProductFirst reals zero terms =
  complexOne reals
complexProductFirst reals (suc n) terms =
  complexMultiply reals
    (complexProductFirst reals n terms)
    (terms n)

module Putnam2015A3Statement
  {R : Set}
  (reals : CompleteOrderedRealField R)
  (analysis : StandardRealAnalysis reals)
  (complexAnalysis : StandardComplexAnalysis reals analysis) where

  angle : Nat -> Nat -> R
  angle a b =
    divide reals
      (multiply reals
        (multiply reals
          (multiply reals
            (fromNat reals twoN)
            (pi analysis))
          (fromNat reals (suc a)))
        (fromNat reals (suc b)))
      (fromNat reals 2015)

  factor : Nat -> Nat -> Complex R
  factor a b =
    complexAdd reals
      (complexOne reals)
      (complexExponential reals analysis
        (complex
          (zeroR reals)
          (angle a b)))

  product : Complex R
  product =
    complexProductFirst reals 2015
      (\ a ->
        complexProductFirst reals 2015
          (factor a))

  baseTwoLogarithm : Complex R
  baseTwoLogarithm =
    complexDivide reals
      (complexLogarithm reals analysis complexAnalysis product)
      (complexLogarithm reals analysis complexAnalysis
        (complexFromReal reals (fromNat reals twoN)))

  solution : Complex R
  solution =
    complexFromReal reals
      (fromNat reals 13725)

  proposition : Set
  proposition =
    baseTwoLogarithm == solution

putnam-2015-a3 : Set1
putnam-2015-a3 =
  (R : Set) ->
  (reals : CompleteOrderedRealField R) ->
  (analysis : StandardRealAnalysis reals) ->
  (complexAnalysis : StandardComplexAnalysis reals analysis) ->
  Putnam2015A3Statement.proposition
    reals
    analysis
    complexAnalysis
