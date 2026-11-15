-- Statement-only formalization of PutnamBench corpus artifact putnam_1976_a6:
-- a twice continuously differentiable real function bounded in absolute value
-- by one and satisfying f(0)^2 + f'(0)^2 = 4 has a point where f + f'' is zero.
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
DerivativeAt {R} reals function point derivativeValue =
  (epsilon : R) ->
  StrictLess reals (zeroR reals) epsilon ->
  Exists R
    (\ delta ->
      StrictLess reals (zeroR reals) delta
      and
      ((x : R) ->
        CloseTo reals point delta x ->
        x != point ->
        CloseTo reals derivativeValue epsilon
          (differenceQuotient reals function point x)))

HasDerivativeAt :
  {R : Set} ->
  CompleteOrderedRealField R ->
  (R -> R) ->
  R ->
  Set
HasDerivativeAt {R} reals function point =
  Exists R
    (\ derivativeValue ->
      DerivativeAt reals function point derivativeValue)

record StandardRealCalculus
  {R : Set}
  (reals : CompleteOrderedRealField R) : Set1 where

  field
    derivative : (R -> R) -> R -> R

    derivative-when-differentiable :
      (function : R -> R) ->
      (point : R) ->
      HasDerivativeAt reals function point ->
      DerivativeAt reals
        function
        point
        (derivative function point)

    derivative-when-not-differentiable :
      (function : R -> R) ->
      (point : R) ->
      Not (HasDerivativeAt reals function point) ->
      derivative function point == zeroR reals

open StandardRealCalculus

TwiceContinuouslyDifferentiable :
  {R : Set} ->
  (reals : CompleteOrderedRealField R) ->
  StandardRealCalculus reals ->
  (R -> R) ->
  Set
TwiceContinuouslyDifferentiable {R} reals calculus function =
  ((point : R) ->
    DerivativeAt reals
      function
      point
      (derivative calculus function point))
  and
  ((point : R) ->
    DerivativeAt reals
      (derivative calculus function)
      point
      (derivative calculus
        (derivative calculus function)
        point))
  and
  Continuous reals
    (derivative calculus
      (derivative calculus function))

AbsoluteValueAtMost :
  {R : Set} ->
  CompleteOrderedRealField R ->
  R ->
  R ->
  Set
AbsoluteValueAtMost reals bound value =
  lessOrEqual reals (negate reals bound) value
  and
  lessOrEqual reals value bound

four :
  {R : Set} ->
  CompleteOrderedRealField R ->
  R
four reals =
  fromNat reals
    (suc (suc (suc (suc zero))))

putnam-1976-a6 : Set1
putnam-1976-a6 =
  (R : Set) ->
  (reals : CompleteOrderedRealField R) ->
  (calculus : StandardRealCalculus reals) ->
  (f : R -> R) ->
  TwiceContinuouslyDifferentiable reals calculus f ->
  ((x : R) ->
    AbsoluteValueAtMost reals
      (oneR reals)
      (f x)) ->
  add reals
    (square reals (f (zeroR reals)))
    (square reals
      (derivative calculus f (zeroR reals)))
    ==
    four reals ->
  Exists R
    (\ y ->
      add reals
        (f y)
        (derivative calculus
          (derivative calculus f)
          y)
      ==
      zeroR reals)
