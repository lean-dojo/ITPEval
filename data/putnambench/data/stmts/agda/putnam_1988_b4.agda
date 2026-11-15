-- Statement-only formalization of PutnamBench corpus artifact putnam_1988_b4:
-- a convergent series of positive real terms remains positive and convergent
-- after raising its nth term to the real exponent n / (n + 1).
-- This file contains no proof.

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
  zero<=N   : {n : Nat} -> zero <=N n
  suc<=sucN : {m n : Nat} -> m <=N n -> suc m <=N suc n

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

sumFromOneThrough :
  {R : Set} ->
  CompleteOrderedRealField R ->
  (Nat -> R) ->
  Nat ->
  R
sumFromOneThrough reals term zero =
  zeroR reals
sumFromOneThrough reals term (suc n) =
  add reals
    (sumFromOneThrough reals term n)
    (term (suc n))

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

Converges :
  {R : Set} ->
  CompleteOrderedRealField R ->
  (Nat -> R) ->
  Set
Converges {R} reals sequence =
  Exists R
    (\ limit -> ConvergesTo reals sequence limit)

SeriesConvergesFromOne :
  {R : Set} ->
  CompleteOrderedRealField R ->
  (Nat -> R) ->
  Set
SeriesConvergesFromOne reals term =
  Converges reals
    (sumFromOneThrough reals term)

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
  ConvergesTo reals
    (\ n -> sumFirst reals n (exponentialTerm reals x))
    value

record StandardRealPowers
  {R : Set}
  (reals : CompleteOrderedRealField R) :
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
  {reals : CompleteOrderedRealField R} ->
  StandardRealPowers reals ->
  R ->
  R ->
  R
realPower {reals = reals} powers base exponent =
  exponential powers
    (multiply reals exponent (logarithm powers base))

PositiveSequence :
  {R : Set} ->
  CompleteOrderedRealField R ->
  (Nat -> R) ->
  Set
PositiveSequence reals a =
  (n : Nat) ->
  oneN <=N n ->
  StrictLess reals (zeroR reals) (a n)

PositiveConvergentSeries :
  {R : Set} ->
  CompleteOrderedRealField R ->
  (Nat -> R) ->
  Set
PositiveConvergentSeries reals a =
  PositiveSequence reals a
  and
  SeriesConvergesFromOne reals a

module Putnam1988B4Statement
  {R : Set}
  (reals : CompleteOrderedRealField R)
  (powers : StandardRealPowers reals) where

  transformedTerm : (Nat -> R) -> Nat -> R
  transformedTerm a n =
    realPower powers
      (a n)
      (divide reals
        (fromNat reals n)
        (fromNat reals (suc n)))

  proposition : Set
  proposition =
    (a : Nat -> R) ->
    PositiveConvergentSeries reals a ->
    PositiveConvergentSeries reals (transformedTerm a)

putnam-1988-b4 : Set1
putnam-1988-b4 =
  (R : Set) ->
  (reals : CompleteOrderedRealField R) ->
  (powers : StandardRealPowers reals) ->
  Putnam1988B4Statement.proposition reals powers
