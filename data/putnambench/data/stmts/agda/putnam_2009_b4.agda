-- Statement-only formalization of PutnamBench corpus artifact putnam_2009_b4
-- (putnambench__agda__putnam_2009_b4): the real vector space of balanced
-- bivariate polynomials of total degree at most 2009 has dimension 2020050.
-- This file contains no proof.

{-# OPTIONS --safe #-}

module Putnam2009B4 where

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

data Fin : Nat -> Set where
  fzero : {n : Nat} -> Fin (suc n)
  fsuc  : {n : Nat} -> Fin n -> Fin (suc n)

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
      (x y : R) ->
      add x y == add y x
    add-associative :
      (x y z : R) ->
      add (add x y) z == add x (add y z)
    add-zero :
      (x : R) ->
      add x zeroR == x
    add-inverse :
      (x : R) ->
      add x (negate x) == zeroR

    multiply-commutative :
      (x y : R) ->
      multiply x y == multiply y x
    multiply-associative :
      (x y z : R) ->
      multiply (multiply x y) z ==
      multiply x (multiply y z)
    multiply-one :
      (x : R) ->
      multiply x oneR == x
    multiply-zero :
      (x : R) ->
      multiply x zeroR == zeroR
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
      (x : R) ->
      lessOrEqual x x
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

sumFin :
  {R : Set} ->
  CompleteOrderedRealField R ->
  (n : Nat) ->
  (Fin n -> R) ->
  R
sumFin reals zero terms =
  zeroR reals
sumFin reals (suc n) terms =
  add reals
    (terms fzero)
    (sumFin reals n
      (\ index ->
        terms (fsuc index)))

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

double : Nat -> Nat
double zero =
  zero
double (suc n) =
  suc (suc (double n))

alternatingSign :
  {R : Set} ->
  CompleteOrderedRealField R ->
  Nat ->
  R
alternatingSign reals zero =
  oneR reals
alternatingSign reals (suc n) =
  negate reals (alternatingSign reals n)

cosineTerm :
  {R : Set} ->
  CompleteOrderedRealField R ->
  R ->
  Nat ->
  R
cosineTerm reals x n =
  divide reals
    (multiply reals
      (alternatingSign reals n)
      (naturalPower reals x (double n)))
    (fromNat reals (factorial (double n)))

sineTerm :
  {R : Set} ->
  CompleteOrderedRealField R ->
  R ->
  Nat ->
  R
sineTerm reals x n =
  divide reals
    (multiply reals
      (alternatingSign reals n)
      (naturalPower reals x (suc (double n))))
    (fromNat reals (factorial (suc (double n))))

SeriesHasSum :
  {R : Set} ->
  CompleteOrderedRealField R ->
  (Nat -> R) ->
  R ->
  Set
SeriesHasSum reals terms value =
  ConvergesTo reals
    (\ n ->
      sumFirst reals n terms)
    value

twoN : Nat
twoN =
  suc (suc zero)

record StandardTrigonometry
  {R : Set}
  (reals : CompleteOrderedRealField R) :
  Set1 where

  field
    sine cosine : R -> R
    pi : R

    sine-series :
      (x : R) ->
      SeriesHasSum reals
        (sineTerm reals x)
        (sine x)
    cosine-series :
      (x : R) ->
      SeriesHasSum reals
        (cosineTerm reals x)
        (cosine x)

    pi-positive :
      StrictLess reals (zeroR reals) pi
    cosine-half-pi :
      cosine
        (divide reals pi (fromNat reals twoN))
      ==
      zeroR reals
    cosine-positive-before-half-pi :
      (x : R) ->
      StrictLess reals (zeroR reals) x ->
      StrictLess reals
        x
        (divide reals pi (fromNat reals twoN)) ->
      StrictLess reals (zeroR reals) (cosine x)

open StandardTrigonometry

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

Polynomial : Set -> Set
Polynomial R =
  Nat -> Nat -> R

PolynomialEqual :
  {R : Set} ->
  Polynomial R ->
  Polynomial R ->
  Set
PolynomialEqual leftPolynomial rightPolynomial =
  (i j : Nat) ->
  leftPolynomial i j == rightPolynomial i j

zeroPolynomial :
  {R : Set} ->
  CompleteOrderedRealField R ->
  Polynomial R
zeroPolynomial reals i j =
  zeroR reals

addPolynomial :
  {R : Set} ->
  CompleteOrderedRealField R ->
  Polynomial R ->
  Polynomial R ->
  Polynomial R
addPolynomial reals leftPolynomial rightPolynomial i j =
  add reals
    (leftPolynomial i j)
    (rightPolynomial i j)

scalePolynomial :
  {R : Set} ->
  CompleteOrderedRealField R ->
  R ->
  Polynomial R ->
  Polynomial R
scalePolynomial reals scalar polynomial i j =
  multiply reals scalar (polynomial i j)

DegreeAtMost :
  {R : Set} ->
  CompleteOrderedRealField R ->
  Polynomial R ->
  Nat ->
  Set
DegreeAtMost reals polynomial degreeBound =
  (i j : Nat) ->
  suc degreeBound <=N i + j ->
  polynomial i j == zeroR reals

evaluateBounded :
  {R : Set} ->
  CompleteOrderedRealField R ->
  Nat ->
  Polynomial R ->
  R ->
  R ->
  R
evaluateBounded reals degreeBound polynomial x y =
  sumFirst reals (suc degreeBound)
    (\ i ->
      sumFirst reals (suc degreeBound)
        (\ j ->
          multiply reals
            (polynomial i j)
            (multiply reals
              (naturalPower reals x i)
              (naturalPower reals y j))))

Balanced :
  {R : Set} ->
  (reals : CompleteOrderedRealField R) ->
  StandardTrigonometry reals ->
  Polynomial R ->
  Set
Balanced {R} reals trigonometry polynomial =
  (radius : R) ->
  StrictLess reals (zeroR reals) radius ->
  IntervalIntegralValue reals
    (zeroR reals)
    (multiply reals
      (fromNat reals twoN)
      (pi trigonometry))
    (\ angle ->
      evaluateBounded reals 2009 polynomial
        (multiply reals radius (cosine trigonometry angle))
        (multiply reals radius (sine trigonometry angle)))
    (zeroR reals)

linearCombination :
  {R : Set} ->
  (reals : CompleteOrderedRealField R) ->
  {n : Nat} ->
  (Fin n -> Polynomial R) ->
  (Fin n -> R) ->
  Polynomial R
linearCombination reals {n} basis coefficients i j =
  sumFin reals n
    (\ index ->
      multiply reals
        (coefficients index)
        (basis index i j))

LinearIndependent :
  {R : Set} ->
  (reals : CompleteOrderedRealField R) ->
  {n : Nat} ->
  (Fin n -> Polynomial R) ->
  Set
LinearIndependent reals basis =
  (coefficients : Fin _ -> _) ->
  PolynomialEqual
    (linearCombination reals basis coefficients)
    (zeroPolynomial reals) ->
  (index : Fin _) ->
  coefficients index == zeroR reals

Spans :
  {R : Set} ->
  (reals : CompleteOrderedRealField R) ->
  (V : Polynomial R -> Set) ->
  {n : Nat} ->
  (Fin n -> Polynomial R) ->
  Set
Spans reals V basis =
  (polynomial : Polynomial _) ->
  V polynomial ->
  Exists (Fin _ -> _)
    (\ coefficients ->
      PolynomialEqual
        (linearCombination reals basis coefficients)
        polynomial)

HasDimension :
  {R : Set} ->
  (reals : CompleteOrderedRealField R) ->
  (V : Polynomial R -> Set) ->
  Nat ->
  Set
HasDimension reals V dimension =
  Exists (Fin dimension -> Polynomial _)
    (\ basis ->
      ((index : Fin dimension) ->
        V (basis index))
      and
      LinearIndependent reals basis
      and
      Spans reals V basis)

putnam-2009-b4 : Set1
putnam-2009-b4 =
  (R : Set) ->
  (reals : CompleteOrderedRealField R) ->
  (trigonometry : StandardTrigonometry reals) ->
  (V : Polynomial R -> Set) ->
  ((polynomial : Polynomial R) ->
    Iff
      (V polynomial)
      (Balanced reals trigonometry polynomial
      and
      DegreeAtMost reals polynomial 2009)) ->
  HasDimension reals V 2020050
