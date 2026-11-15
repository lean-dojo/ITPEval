-- Statement-only formalization of PutnamBench corpus artifact putnam_2012_a3:
-- the continuous functions on [-1,1] satisfying the given functional equation,
-- normalization at zero, and finite left limit at one have the unique closed
-- form sqrt(1 - x^2). This file contains no proof.

{-# OPTIONS --safe #-}

module Putnam2012A3 where

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
    negate inverse squareRoot : R -> R
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

    square-root-nonnegative :
      (x : R) ->
      lessOrEqual zeroR (squareRoot x)
    square-root-square :
      (x : R) ->
      lessOrEqual zeroR x ->
      multiply (squareRoot x) (squareRoot x) == x
    square-root-nonpositive :
      (x : R) ->
      lessOrEqual x zeroR ->
      squareRoot x == zeroR
    square-root-unique :
      (x y : R) ->
      lessOrEqual zeroR y ->
      multiply y y == x ->
      y == squareRoot x

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

two :
  {R : Set} ->
  CompleteOrderedRealField R ->
  R
two reals =
  add reals (oneR reals) (oneR reals)

maximum :
  {R : Set} ->
  CompleteOrderedRealField R ->
  R ->
  R ->
  R
maximum reals x y with order-total reals x y
... | left _ =
  y
... | right _ =
  x

absoluteValue :
  {R : Set} ->
  CompleteOrderedRealField R ->
  R ->
  R
absoluteValue reals x =
  maximum reals x (negate reals x)

StrictLess :
  {R : Set} ->
  CompleteOrderedRealField R ->
  R ->
  R ->
  Set
StrictLess reals x y =
  lessOrEqual reals x y and x != y

Distance :
  {R : Set} ->
  CompleteOrderedRealField R ->
  R ->
  R ->
  R
Distance reals x y =
  absoluteValue reals (subtract reals x y)

InUnitInterval :
  {R : Set} ->
  CompleteOrderedRealField R ->
  R ->
  Set
InUnitInterval reals x =
  lessOrEqual reals (negate reals (oneR reals)) x
  and
  lessOrEqual reals x (oneR reals)

ContinuousOnUnitInterval :
  {R : Set} ->
  CompleteOrderedRealField R ->
  (R -> R) ->
  Set
ContinuousOnUnitInterval {R} reals function =
  (point : R) ->
  InUnitInterval reals point ->
  (epsilon : R) ->
  StrictLess reals (zeroR reals) epsilon ->
  Exists R
    (\ delta ->
      StrictLess reals (zeroR reals) delta
      and
      ((x : R) ->
        InUnitInterval reals x ->
        StrictLess reals
          (Distance reals x point)
          delta ->
        StrictLess reals
          (Distance reals (function x) (function point))
          epsilon))

FiniteLeftLimitAtOne :
  {R : Set} ->
  CompleteOrderedRealField R ->
  (R -> R) ->
  Set
FiniteLeftLimitAtOne {R} reals function =
  Exists R
    (\ limit ->
      (epsilon : R) ->
      StrictLess reals (zeroR reals) epsilon ->
      Exists R
        (\ delta ->
          StrictLess reals (zeroR reals) delta
          and
          ((x : R) ->
            StrictLess reals
              (subtract reals
                (oneR reals)
                delta)
              x ->
            StrictLess reals x (oneR reals) ->
            StrictLess reals
              (Distance reals
                (divide reals
                  (function x)
                  (squareRoot reals
                    (subtract reals
                      (oneR reals)
                      x)))
                limit)
              epsilon)))

functionalArgument :
  {R : Set} ->
  CompleteOrderedRealField R ->
  R ->
  R
functionalArgument reals x =
  divide reals
    (square reals x)
    (subtract reals
      (two reals)
      (square reals x))

functionalCoefficient :
  {R : Set} ->
  CompleteOrderedRealField R ->
  R ->
  R
functionalCoefficient reals x =
  divide reals
    (subtract reals
      (two reals)
      (square reals x))
    (two reals)

record SatisfiesConditions
  {R : Set}
  (reals : CompleteOrderedRealField R)
  (function : R -> R) :
  Set where

  field
    continuous-on-interval :
      ContinuousOnUnitInterval reals function

    functional-equation :
      (x : R) ->
      InUnitInterval reals x ->
      function x ==
      multiply reals
        (functionalCoefficient reals x)
        (function (functionalArgument reals x))

    normalized-at-zero :
      function (zeroR reals) == oneR reals

    finite-left-limit :
      FiniteLeftLimitAtOne reals function

solution :
  {R : Set} ->
  CompleteOrderedRealField R ->
  R ->
  R
solution reals x =
  squareRoot reals
    (subtract reals
      (oneR reals)
      (square reals x))

putnam-2012-a3 : Set1
putnam-2012-a3 =
  (R : Set) ->
  (reals : CompleteOrderedRealField R) ->
  SatisfiesConditions reals (solution reals)
  and
  ((function : R -> R) ->
    SatisfiesConditions reals function ->
    (x : R) ->
    InUnitInterval reals x ->
    function x == solution reals x)
