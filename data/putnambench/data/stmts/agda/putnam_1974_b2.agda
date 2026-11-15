-- Statement-only formalization of PutnamBench corpus artifact putnam_1974_b2:
-- a continuously differentiable real function for which (y')^2 + y^3 tends
-- to zero at positive infinity has both y and y' tending to zero there.
-- This file contains no proof.

{-# OPTIONS --safe #-}

open import Agda.Builtin.Equality renaming (_≡_ to _==_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)

infix 4 _!=_
infixr 3 _and_
infixr 2 _or_

data Bottom : Set where

record Top : Set where
  constructor top

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
        CloseTo reals (function point) epsilon (function x)))

Continuous :
  {R : Set} ->
  CompleteOrderedRealField R ->
  (R -> R) ->
  Set
Continuous {R} reals function =
  (point : R) ->
  ContinuousAt reals function point

whole :
  {A : Set} ->
  A ->
  Set
whole _ =
  Top

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

DerivativeWithinAt :
  {R : Set} ->
  CompleteOrderedRealField R ->
  (R -> R) ->
  (R -> Set) ->
  R ->
  R ->
  Set
DerivativeWithinAt {R} reals function domain point derivativeValue =
  (epsilon : R) ->
  StrictLess reals (zeroR reals) epsilon ->
  Exists R
    (\ delta ->
      StrictLess reals (zeroR reals) delta
      and
      ((x : R) ->
        domain x ->
        CloseTo reals point delta x ->
        x != point ->
        CloseTo reals derivativeValue epsilon
          (differenceQuotient reals function point x)))

DerivativeAt :
  {R : Set} ->
  CompleteOrderedRealField R ->
  (R -> R) ->
  R ->
  R ->
  Set
DerivativeAt reals function point derivativeValue =
  DerivativeWithinAt
    reals
    function
    whole
    point
    derivativeValue

record StandardRealCalculus
  {R : Set}
  (reals : CompleteOrderedRealField R) : Set1 where

  field
    derivative : (R -> R) -> R -> R
    derivative-correct :
      (function : R -> R) ->
      (point derivativeValue : R) ->
      DerivativeAt reals function point derivativeValue ->
      derivative function point == derivativeValue
    derivative-totalized-at-zero :
      (function : R -> R) ->
      (point : R) ->
      Not (Exists R (DerivativeAt reals function point)) ->
      derivative function point == zeroR reals

open StandardRealCalculus

C1Differentiable :
  {R : Set} ->
  (reals : CompleteOrderedRealField R) ->
  StandardRealCalculus reals ->
  (R -> R) ->
  Set
C1Differentiable {R} reals calculus function =
  ((point : R) ->
    DerivativeAt reals function point
      (derivative calculus function point))
  and
  Continuous reals (derivative calculus function)

TendsAtPositiveInfinity :
  {R : Set} ->
  CompleteOrderedRealField R ->
  (R -> R) ->
  R ->
  Set
TendsAtPositiveInfinity {R} reals function limit =
  (epsilon : R) ->
  StrictLess reals (zeroR reals) epsilon ->
  Exists R
    (\ cutoff ->
      (x : R) ->
      lessOrEqual reals cutoff x ->
      CloseTo reals limit epsilon (function x))

square :
  {R : Set} ->
  CompleteOrderedRealField R ->
  R ->
  R
square reals x =
  multiply reals x x

cube :
  {R : Set} ->
  CompleteOrderedRealField R ->
  R ->
  R
cube reals x =
  multiply reals (square reals x) x

energyExpression :
  {R : Set} ->
  (reals : CompleteOrderedRealField R) ->
  StandardRealCalculus reals ->
  (R -> R) ->
  R ->
  R
energyExpression reals calculus y x =
  add reals
    (square reals (derivative calculus y x))
    (cube reals (y x))

putnam-1974-b2 : Set1
putnam-1974-b2 =
  (R : Set) ->
  (reals : CompleteOrderedRealField R) ->
  (calculus : StandardRealCalculus reals) ->
  (y : R -> R) ->
  C1Differentiable reals calculus y ->
  TendsAtPositiveInfinity reals
    (energyExpression reals calculus y)
    (zeroR reals) ->
  TendsAtPositiveInfinity reals y (zeroR reals)
  and
  TendsAtPositiveInfinity reals
    (derivative calculus y)
    (zeroR reals)
