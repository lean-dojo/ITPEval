-- Statement-only formalization of PutnamBench corpus artifact putnam_1999_b4
-- (putnambench__agda__putnam_1999_b4): a positive real function with positive
-- first three derivatives and continuous third derivative, satisfying
-- f'''(x) <= f(x), has f'(x) < 2 f(x) for every real x.
-- This file contains no proof.

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

twoN : Nat
twoN =
  suc (suc zero)

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

Positive :
  {R : Set} ->
  CompleteOrderedRealField R ->
  R ->
  Set
Positive reals x =
  StrictLess reals (zeroR reals) x

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
  Positive reals epsilon ->
  Exists R
    (\ delta ->
      Positive reals delta
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
DerivativeAt {R} reals function point derivativeValue =
  (epsilon : R) ->
  Positive reals epsilon ->
  Exists R
    (\ delta ->
      Positive reals delta
      and
      ((x : R) ->
        CloseTo reals point delta x ->
        x != point ->
        CloseTo reals derivativeValue epsilon
          (differenceQuotient reals function point x)))

record ContinuousThirdDerivative
  {R : Set}
  (reals : CompleteOrderedRealField R)
  (function : R -> R) :
  Set where

  field
    firstDerivative : R -> R
    secondDerivative : R -> R
    thirdDerivative : R -> R

    first-derivative-correct :
      (x : R) ->
      DerivativeAt reals
        function
        x
        (firstDerivative x)

    second-derivative-correct :
      (x : R) ->
      DerivativeAt reals
        firstDerivative
        x
        (secondDerivative x)

    third-derivative-correct :
      (x : R) ->
      DerivativeAt reals
        secondDerivative
        x
        (thirdDerivative x)

    third-derivative-continuous :
      Continuous reals thirdDerivative

open ContinuousThirdDerivative

putnam-1999-b4 : Set1
putnam-1999-b4 =
  (R : Set) ->
  (reals : CompleteOrderedRealField R) ->
  (f : R -> R) ->
  (smooth : ContinuousThirdDerivative reals f) ->
  ((x : R) ->
    Positive reals (f x)
    and
    Positive reals (firstDerivative smooth x)
    and
    Positive reals (secondDerivative smooth x)
    and
    Positive reals (thirdDerivative smooth x)) ->
  ((x : R) ->
    lessOrEqual reals
      (thirdDerivative smooth x)
      (f x)) ->
  (x : R) ->
  StrictLess reals
    (firstDerivative smooth x)
    (multiply reals
      (fromNat reals twoN)
      (f x))
