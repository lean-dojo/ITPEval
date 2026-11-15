-- Statement-only formalization of PutnamBench corpus artifact putnam_1965_b1:
-- the limit of the integrals over unit cubes of a squared cosine of the
-- normalized coordinate sum is one half. This file contains no proof.

{-# OPTIONS --safe #-}

open import Agda.Builtin.Equality renaming (_≡_ to _==_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)

infix 4 _!=_ _<=N_
infixr 3 _and_
infixr 5 _::_

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

data Vec (A : Set) : Nat -> Set where
  []    : Vec A zero
  _::_  : {n : Nat} -> A -> Vec A n -> Vec A (suc n)

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
      (x y z : R) -> add (add x y) z == add x (add y z)
    add-zero :
      (x : R) -> add x zeroR == x
    add-inverse :
      (x : R) -> add x (negate x) == zeroR

    multiply-commutative :
      (x y : R) -> multiply x y == multiply y x
    multiply-associative :
      (x y z : R) ->
      multiply (multiply x y) z == multiply x (multiply y z)
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
      (n : Nat) -> fromNat (suc n) == add (fromNat n) oneR
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

square :
  {R : Set} ->
  CompleteOrderedField R ->
  R ->
  R
square reals x =
  multiply reals x x

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
  suc zero
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

double : Nat -> Nat
double zero =
  zero
double (suc n) =
  suc (suc (double n))

alternatingSign :
  {R : Set} ->
  CompleteOrderedField R ->
  Nat ->
  R
alternatingSign reals zero =
  oneR reals
alternatingSign reals (suc n) =
  negate reals (alternatingSign reals n)

cosineTerm :
  {R : Set} ->
  CompleteOrderedField R ->
  R ->
  Nat ->
  R
cosineTerm reals x n =
  divide reals
    (multiply reals
      (alternatingSign reals n)
      (naturalPower reals x (double n)))
    (fromNat reals (factorial (double n)))

two : Nat
two =
  suc (suc zero)

record StandardCosine
  {R : Set}
  (reals : CompleteOrderedField R) :
  Set1 where

  field
    cosine : R -> R
    pi : R

    cosine-series :
      (x : R) ->
      SeriesHasSum reals
        (cosineTerm reals x)
        (cosine x)

    pi-positive :
      StrictLess reals (zeroR reals) pi
    cosine-half-pi :
      cosine
        (divide reals pi (fromNat reals two))
      ==
      zeroR reals
    cosine-positive-before-half-pi :
      (x : R) ->
      StrictLess reals (zeroR reals) x ->
      StrictLess reals
        x
        (divide reals pi (fromNat reals two)) ->
      StrictLess reals (zeroR reals) (cosine x)

open StandardCosine

uniformUnitSum :
  {R : Set} ->
  CompleteOrderedField R ->
  (R -> R) ->
  Nat ->
  R
uniformUnitSum reals function pieces =
  divide reals
    (sumFirst reals pieces
      (\ k ->
        function
          (divide reals
            (fromNat reals k)
            (fromNat reals pieces))))
    (fromNat reals pieces)

RiemannIntegralValue :
  {R : Set} ->
  CompleteOrderedField R ->
  (R -> R) ->
  R ->
  Set
RiemannIntegralValue reals function integralValue =
  ConvergesTo reals
    (\ n -> uniformUnitSum reals function (suc n))
    integralValue

RiemannIntegrable :
  {R : Set} ->
  CompleteOrderedField R ->
  (R -> R) ->
  Set
RiemannIntegrable {R} reals function =
  Exists R
    (\ integralValue ->
      RiemannIntegralValue reals function integralValue)

record UnitIntervalIntegration
  {R : Set}
  (reals : CompleteOrderedField R) :
  Set1 where

  field
    integral : (R -> R) -> R
    integral-is-riemann :
      (function : R -> R) ->
      RiemannIntegrable reals function ->
      RiemannIntegralValue reals function (integral function)

open UnitIntervalIntegration

cubeIntegral :
  {R : Set} ->
  (reals : CompleteOrderedField R) ->
  UnitIntervalIntegration reals ->
  (dimension : Nat) ->
  (Vec R dimension -> R) ->
  R
cubeIntegral reals integration zero function =
  function []
cubeIntegral reals integration (suc dimension) function =
  integral integration
    (\ x ->
      cubeIntegral reals integration dimension
        (\ xs -> function (x :: xs)))

sumCoordinates :
  {R : Set} ->
  CompleteOrderedField R ->
  {dimension : Nat} ->
  Vec R dimension ->
  R
sumCoordinates reals [] =
  zeroR reals
sumCoordinates reals (x :: xs) =
  add reals x (sumCoordinates reals xs)

putnamIntegrand :
  {R : Set} ->
  (reals : CompleteOrderedField R) ->
  StandardCosine reals ->
  (n : Nat) ->
  Vec R (suc n) ->
  R
putnamIntegrand reals analysis n point =
  square reals
    (cosine analysis
      (multiply reals
        (divide reals
          (pi analysis)
          (multiply reals
            (fromNat reals two)
            (fromNat reals (suc n))))
        (sumCoordinates reals point)))

putnam-1965-b1-solution :
  {R : Set} ->
  CompleteOrderedField R ->
  R
putnam-1965-b1-solution reals =
  divide reals
    (oneR reals)
    (fromNat reals two)

putnam-1965-b1 : Set1
putnam-1965-b1 =
  (R : Set) ->
  (reals : CompleteOrderedField R) ->
  (analysis : StandardCosine reals) ->
  (integration : UnitIntervalIntegration reals) ->
  ConvergesTo reals
    (\ n ->
      cubeIntegral reals integration (suc n)
        (putnamIntegrand reals analysis n))
    (putnam-1965-b1-solution reals)
