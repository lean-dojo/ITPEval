-- Statement-only formalization of PutnamBench corpus artifact putnam_2022_b6
-- (putnambench__agda__putnam_2022_b6): classification of the continuous
-- positive-real functions satisfying the stated two-variable functional
-- equation. This file contains no proof.

{-# OPTIONS --safe #-}

module Putnam2022B6 where

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

Positive :
  {R : Set} ->
  CompleteOrderedRealField R ->
  R ->
  Set
Positive reals x =
  StrictLess reals (zeroR reals) x

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

Distance :
  {R : Set} ->
  CompleteOrderedRealField R ->
  R ->
  R ->
  R
Distance reals x y =
  absoluteValue reals (subtract reals x y)

MapsPositiveToPositive :
  {R : Set} ->
  CompleteOrderedRealField R ->
  (R -> R) ->
  Set
MapsPositiveToPositive {R} reals f =
  (x : R) ->
  Positive reals x ->
  Positive reals (f x)

ContinuousOnPositive :
  {R : Set} ->
  CompleteOrderedRealField R ->
  (R -> R) ->
  Set
ContinuousOnPositive {R} reals f =
  (point : R) ->
  Positive reals point ->
  (epsilon : R) ->
  Positive reals epsilon ->
  Exists R
    (\ delta ->
      Positive reals delta
      and
      ((x : R) ->
        Positive reals x ->
        StrictLess reals
          (Distance reals x point)
          delta ->
        StrictLess reals
          (Distance reals (f x) (f point))
          epsilon))

FunctionalEquation :
  {R : Set} ->
  CompleteOrderedRealField R ->
  (R -> R) ->
  Set
FunctionalEquation {R} reals f =
  (x y : R) ->
  Positive reals x ->
  Positive reals y ->
  add reals
    (f (multiply reals x (f y)))
    (f (multiply reals y (f x)))
  ==
  add reals
    (oneR reals)
    (f (add reals x y))

SatisfiesConditions :
  {R : Set} ->
  CompleteOrderedRealField R ->
  (R -> R) ->
  Set
SatisfiesConditions reals f =
  MapsPositiveToPositive reals f
  and
  ContinuousOnPositive reals f
  and
  FunctionalEquation reals f

HasSolutionForm :
  {R : Set} ->
  CompleteOrderedRealField R ->
  (R -> R) ->
  Set
HasSolutionForm {R} reals f =
  Exists R
    (\ c ->
      lessOrEqual reals (zeroR reals) c
      and
      ((x : R) ->
        Positive reals x ->
        f x ==
        divide reals
          (oneR reals)
          (add reals
            (oneR reals)
            (multiply reals c x))))

putnam-2022-b6 : Set1
putnam-2022-b6 =
  (R : Set) ->
  (reals : CompleteOrderedRealField R) ->
  (f : R -> R) ->
  Iff
    (SatisfiesConditions reals f)
    (HasSolutionForm reals f)
