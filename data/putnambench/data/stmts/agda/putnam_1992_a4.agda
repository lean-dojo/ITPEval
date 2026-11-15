-- Statement-only formalization of PutnamBench corpus artifact putnam_1992_a4
-- (putnambench__agda__putnam_1992_a4): derivatives at zero of a smooth real
-- function prescribed at the reciprocal positive integers. This file contains
-- no proof.

{-# OPTIONS --safe #-}

open import Agda.Builtin.Equality renaming (_≡_ to _==_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)

infix 4 _!=_
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

data Positive : Nat -> Set where
  positive : (n : Nat) -> Positive (suc n)

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

square :
  {R : Set} ->
  CompleteOrderedRealField R ->
  R ->
  R
square reals x =
  multiply reals x x

naturalPower :
  {R : Set} ->
  CompleteOrderedRealField R ->
  R ->
  Nat ->
  R
naturalPower reals base zero =
  oneR reals
naturalPower reals base (suc exponent) =
  multiply reals base (naturalPower reals base exponent)

factorial : Nat -> Nat
factorial zero =
  suc zero
factorial (suc n) =
  suc n * factorial n

half : Nat -> Nat
half zero =
  zero
half (suc zero) =
  zero
half (suc (suc n)) =
  suc (half n)

data Parity : Set where
  evenParity oddParity : Parity

oppositeParity : Parity -> Parity
oppositeParity evenParity =
  oddParity
oppositeParity oddParity =
  evenParity

parity : Nat -> Parity
parity zero =
  evenParity
parity (suc n) =
  oppositeParity (parity n)

putnam-1992-a4-solution :
  {R : Set} ->
  CompleteOrderedRealField R ->
  Nat ->
  R
putnam-1992-a4-solution reals k with parity k
... | evenParity =
  multiply reals
    (naturalPower reals
      (negate reals (oneR reals))
      (half k))
    (fromNat reals (factorial k))
... | oddParity =
  zeroR reals

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

ContinuousAt :
  {R : Set} ->
  CompleteOrderedRealField R ->
  (R -> R) ->
  R ->
  Set
ContinuousAt {R} reals function point =
  (epsilon : R) ->
  StrictLess reals (zeroR reals) epsilon ->
  Exists R
    (\ delta ->
      StrictLess reals (zeroR reals) delta
      and
      ((x : R) ->
        CloseTo reals point delta x ->
        CloseTo reals
          (function point)
          epsilon
          (function x)))

Continuous :
  {R : Set} ->
  CompleteOrderedRealField R ->
  (R -> R) ->
  Set
Continuous {R} reals function =
  (point : R) ->
  ContinuousAt reals function point

differenceQuotient :
  {R : Set} ->
  CompleteOrderedRealField R ->
  (R -> R) ->
  R ->
  R ->
  R
differenceQuotient reals function point x =
  divide reals
    (subtract reals (function x) (function point))
    (subtract reals x point)

DerivativeAt :
  {R : Set} ->
  CompleteOrderedRealField R ->
  (R -> R) ->
  R ->
  R ->
  Set
DerivativeAt {R} reals function point derivative =
  (epsilon : R) ->
  StrictLess reals (zeroR reals) epsilon ->
  Exists R
    (\ delta ->
      StrictLess reals (zeroR reals) delta
      and
      ((x : R) ->
        CloseTo reals point delta x ->
        x != point ->
        CloseTo reals derivative epsilon
          (differenceQuotient reals function point x)))

record SmoothDerivativeTower
  {R : Set}
  (reals : CompleteOrderedRealField R)
  (function : R -> R)
  (derivatives : Nat -> R -> R) :
  Set where

  field
    order-zero :
      (x : R) ->
      derivatives zero x == function x

    derivative-step :
      (k : Nat) ->
      (x : R) ->
      DerivativeAt reals
        (derivatives k)
        x
        (derivatives (suc k) x)

    every-order-continuous :
      (k : Nat) ->
      Continuous reals (derivatives k)

InfinitelyDifferentiable :
  {R : Set} ->
  CompleteOrderedRealField R ->
  (R -> R) ->
  Set
InfinitelyDifferentiable {R} reals function =
  Exists (Nat -> R -> R)
    (SmoothDerivativeTower reals function)

SampleValues :
  {R : Set} ->
  CompleteOrderedRealField R ->
  (R -> R) ->
  Set
SampleValues {R} reals function =
  (n : Nat) ->
  Positive n ->
  function
    (divide reals
      (oneR reals)
      (fromNat reals n))
  ==
  divide reals
    (square reals (fromNat reals n))
    (add reals
      (square reals (fromNat reals n))
      (oneR reals))

DerivativeValueAtOrder :
  {R : Set} ->
  CompleteOrderedRealField R ->
  (R -> R) ->
  Nat ->
  R ->
  Set
DerivativeValueAtOrder {R} reals function k derivativeValue =
  (derivatives : Nat -> R -> R) ->
  SmoothDerivativeTower reals function derivatives ->
  derivatives k (zeroR reals) == derivativeValue

putnam-1992-a4 : Set1
putnam-1992-a4 =
  (R : Set) ->
  (reals : CompleteOrderedRealField R) ->
  (f : R -> R) ->
  InfinitelyDifferentiable reals f ->
  SampleValues reals f ->
  (k : Nat) ->
  Positive k ->
  DerivativeValueAtOrder reals f k
    (putnam-1992-a4-solution reals k)
