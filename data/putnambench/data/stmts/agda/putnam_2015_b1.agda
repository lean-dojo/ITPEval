-- Statement-only formalization of PutnamBench corpus artifact putnam_2015_b1
-- (putnambench__agda__putnam_2015_b1): a three-times differentiable real
-- function with five distinct zeros makes f + 6f' + 12f'' + 8f''' have two
-- distinct real zeros. This file contains no proof.

{-# OPTIONS --safe #-}

module Main where

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
DerivativeAt {R} reals function point derivative-value =
  (epsilon : R) ->
  StrictLess reals (zeroR reals) epsilon ->
  Exists R
    (\ delta ->
      StrictLess reals (zeroR reals) delta
      and
      ((x : R) ->
        CloseTo reals point delta x ->
        x != point ->
        CloseTo reals derivative-value epsilon
          (differenceQuotient reals function point x)))

record ThreeTimesDifferentiable
  {R : Set}
  (reals : CompleteOrderedRealField R)
  (function : R -> R) :
  Set where

  field
    firstDerivative secondDerivative thirdDerivative : R -> R

    first-derivative-correct :
      (x : R) ->
      DerivativeAt reals function x (firstDerivative x)
    second-derivative-correct :
      (x : R) ->
      DerivativeAt reals firstDerivative x (secondDerivative x)
    third-derivative-correct :
      (x : R) ->
      DerivativeAt reals secondDerivative x (thirdDerivative x)

open ThreeTimesDifferentiable

record FiveDistinctZeros
  {R : Set}
  (reals : CompleteOrderedRealField R)
  (function : R -> R) :
  Set where

  field
    zero1 zero2 zero3 zero4 zero5 : R

    zero1-is-zero : function zero1 == zeroR reals
    zero2-is-zero : function zero2 == zeroR reals
    zero3-is-zero : function zero3 == zeroR reals
    zero4-is-zero : function zero4 == zeroR reals
    zero5-is-zero : function zero5 == zeroR reals

    zero1!=zero2 : zero1 != zero2
    zero1!=zero3 : zero1 != zero3
    zero1!=zero4 : zero1 != zero4
    zero1!=zero5 : zero1 != zero5
    zero2!=zero3 : zero2 != zero3
    zero2!=zero4 : zero2 != zero4
    zero2!=zero5 : zero2 != zero5
    zero3!=zero4 : zero3 != zero4
    zero3!=zero5 : zero3 != zero5
    zero4!=zero5 : zero4 != zero5

record TwoDistinctZeros
  {R : Set}
  (reals : CompleteOrderedRealField R)
  (function : R -> R) :
  Set where

  field
    zero1 zero2 : R
    distinct : zero1 != zero2
    zero1-is-zero : function zero1 == zeroR reals
    zero2-is-zero : function zero2 == zeroR reals

linearCombination :
  {R : Set} ->
  (reals : CompleteOrderedRealField R) ->
  (function : R -> R) ->
  ThreeTimesDifferentiable reals function ->
  R ->
  R
linearCombination reals function derivatives x =
  add reals
    (function x)
    (add reals
      (multiply reals
        (fromNat reals 6)
        (firstDerivative derivatives x))
      (add reals
        (multiply reals
          (fromNat reals 12)
          (secondDerivative derivatives x))
        (multiply reals
          (fromNat reals 8)
          (thirdDerivative derivatives x))))

putnam-2015-b1 : Set1
putnam-2015-b1 =
  (R : Set) ->
  (reals : CompleteOrderedRealField R) ->
  (function : R -> R) ->
  (derivatives : ThreeTimesDifferentiable reals function) ->
  FiveDistinctZeros reals function ->
  TwoDistinctZeros reals
    (linearCombination reals function derivatives)
