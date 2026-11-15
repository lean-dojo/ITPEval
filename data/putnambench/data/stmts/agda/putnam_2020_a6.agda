-- Statement-only formalization of PutnamBench corpus artifact putnam_2020_a6
-- (putnambench__agda__putnam_2020_a6): the least uniform upper bound of the
-- specified finite trigonometric sums is pi divided by four. This file
-- contains no proof.

{-# OPTIONS --safe #-}

module Main where

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
sumFirst reals zero terms =
  zeroR reals
sumFirst reals (suc n) terms =
  add reals
    (sumFirst reals n terms)
    (terms n)

factorial : Nat -> Nat
factorial zero =
  oneN
factorial (suc n) =
  suc n * factorial n

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

alternate :
  {R : Set} ->
  CompleteOrderedRealField R ->
  Nat ->
  R ->
  R
alternate reals zero x =
  x
alternate reals (suc n) x =
  negate reals (alternate reals n x)

evenExponent : Nat -> Nat
evenExponent n =
  n + n

oddExponent : Nat -> Nat
oddExponent n =
  suc (evenExponent n)

sineTerm :
  {R : Set} ->
  CompleteOrderedRealField R ->
  R ->
  Nat ->
  R
sineTerm reals x n =
  alternate reals n
    (divide reals
      (naturalPower reals x (oddExponent n))
      (fromNat reals (factorial (oddExponent n))))

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
SeriesHasSum reals terms value =
  ConvergesTo reals
    (\ n -> sumFirst reals n terms)
    value

record StandardSine
  {R : Set}
  (reals : CompleteOrderedRealField R) :
  Set1 where

  field
    sine : R -> R
    pi : R

    sine-is-power-series :
      (x : R) ->
      SeriesHasSum reals
        (sineTerm reals x)
        (sine x)

    pi-positive :
      StrictLess reals (zeroR reals) pi
    sine-pi-zero :
      sine pi == zeroR reals
    pi-is-first-positive-sine-zero :
      (x : R) ->
      StrictLess reals (zeroR reals) x ->
      sine x == zeroR reals ->
      lessOrEqual reals pi x

open StandardSine

IsLeastUpperBound :
  {R : Set} ->
  CompleteOrderedRealField R ->
  (R -> Set) ->
  R ->
  Set
IsLeastUpperBound {R} reals property bound =
  ((value : R) ->
    property value ->
    lessOrEqual reals value bound)
  and
  ((upper : R) ->
    ((value : R) ->
      property value ->
      lessOrEqual reals value upper) ->
    lessOrEqual reals bound upper)

module Putnam2020A6Statement
  {R : Set}
  (reals : CompleteOrderedRealField R)
  (trigonometry : StandardSine reals) where

  half : R
  half =
    divide reals
      (oneR reals)
      (fromNat reals twoN)

  oddNatural : Nat -> Nat
  oddNatural n =
    suc (n + n)

  summand : Nat -> R -> Nat -> R
  summand N x n =
    multiply reals
      (divide reals
        (subtract reals
          (add reals (fromNat reals N) half)
          (fromNat reals n))
        (multiply reals
          (fromNat reals (suc N))
          (fromNat reals (oddNatural n))))
      (sine trigonometry
        (multiply reals
          (fromNat reals (oddNatural n))
          x))

  finiteTrigonometricSum : Nat -> R -> R
  finiteTrigonometricSum N x =
    sumFirst reals
      (suc N)
      (summand N x)

  IsPositiveIndexValue : R -> Set
  IsPositiveIndexValue value =
    Exists Nat
      (\ positiveIndexTail ->
        Exists R
          (\ x ->
            value ==
            finiteTrigonometricSum
              (suc positiveIndexTail)
              x))

  solution : R
  solution =
    divide reals
      (pi trigonometry)
      (fromNat reals fourN)

  proposition : Set
  proposition =
    IsLeastUpperBound reals
      IsPositiveIndexValue
      solution

putnam-2020-a6 : Set1
putnam-2020-a6 =
  (R : Set) ->
  (reals : CompleteOrderedRealField R) ->
  (trigonometry : StandardSine reals) ->
  Putnam2020A6Statement.proposition reals trigonometry
