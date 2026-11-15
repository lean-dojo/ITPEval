-- Statement-only formalization of PutnamBench corpus artifact putnam_2018_b5
-- (putnambench__agda__putnam_2018_b5): a continuously differentiable map
-- from the real plane to itself whose positive partial derivatives satisfy
-- the stated quadratic inequality is injective. This file contains no proof.

{-# OPTIONS --safe #-}

module Putnam2018B5 where

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

record Point (R : Set) : Set where
  constructor point
  field
    x1 : R
    x2 : R

open Point

ClosePoint :
  {R : Set} ->
  CompleteOrderedRealField R ->
  Point R ->
  R ->
  Point R ->
  Set
ClosePoint reals center radius p =
  CloseTo reals (x1 center) radius (x1 p)
  and
  CloseTo reals (x2 center) radius (x2 p)

ContinuousAt :
  {R : Set} ->
  CompleteOrderedRealField R ->
  (Point R -> R) ->
  Point R ->
  Set
ContinuousAt {R} reals function center =
  (epsilon : R) ->
  StrictLess reals (zeroR reals) epsilon ->
  Exists R
    (\ delta ->
      StrictLess reals (zeroR reals) delta
      and
      ((p : Point R) ->
        ClosePoint reals center delta p ->
        CloseTo reals
          (function center)
          epsilon
          (function p)))

slice11 :
  {R : Set} ->
  (Point R -> Point R) ->
  Point R ->
  R ->
  R
slice11 function p t =
  x1 (function (point t (x2 p)))

slice12 :
  {R : Set} ->
  (Point R -> Point R) ->
  Point R ->
  R ->
  R
slice12 function p t =
  x1 (function (point (x1 p) t))

slice21 :
  {R : Set} ->
  (Point R -> Point R) ->
  Point R ->
  R ->
  R
slice21 function p t =
  x2 (function (point t (x2 p)))

slice22 :
  {R : Set} ->
  (Point R -> Point R) ->
  Point R ->
  R ->
  R
slice22 function p t =
  x2 (function (point (x1 p) t))

record PartialDerivativeData
  {R : Set}
  (reals : CompleteOrderedRealField R)
  (function : Point R -> Point R) : Set where
  field
    d11 d12 d21 d22 : Point R -> R

    derivative11 :
      (p : Point R) ->
      DerivativeAt reals
        (slice11 function p)
        (x1 p)
        (d11 p)
    derivative12 :
      (p : Point R) ->
      DerivativeAt reals
        (slice12 function p)
        (x2 p)
        (d12 p)
    derivative21 :
      (p : Point R) ->
      DerivativeAt reals
        (slice21 function p)
        (x1 p)
        (d21 p)
    derivative22 :
      (p : Point R) ->
      DerivativeAt reals
        (slice22 function p)
        (x2 p)
        (d22 p)

    continuous11 :
      (p : Point R) ->
      ContinuousAt reals d11 p
    continuous12 :
      (p : Point R) ->
      ContinuousAt reals d12 p
    continuous21 :
      (p : Point R) ->
      ContinuousAt reals d21 p
    continuous22 :
      (p : Point R) ->
      ContinuousAt reals d22 p

open PartialDerivativeData

AllPartialsPositive :
  {R : Set} ->
  {reals : CompleteOrderedRealField R} ->
  {function : Point R -> Point R} ->
  PartialDerivativeData reals function ->
  Set
AllPartialsPositive {R = R} {reals = reals} derivatives =
  (p : Point R) ->
  StrictLess reals (zeroR reals) (d11 derivatives p)
  and
  StrictLess reals (zeroR reals) (d12 derivatives p)
  and
  StrictLess reals (zeroR reals) (d21 derivatives p)
  and
  StrictLess reals (zeroR reals) (d22 derivatives p)

four : Nat
four =
  suc (suc (suc (suc zero)))

quarter :
  {R : Set} ->
  CompleteOrderedRealField R ->
  R
quarter reals =
  inverse reals (fromNat reals four)

QuadraticInequality :
  {R : Set} ->
  {reals : CompleteOrderedRealField R} ->
  {function : Point R -> Point R} ->
  PartialDerivativeData reals function ->
  Set
QuadraticInequality {R = R} {reals = reals} derivatives =
  (p : Point R) ->
  StrictLess reals
    (zeroR reals)
    (subtract reals
      (multiply reals
        (d11 derivatives p)
        (d22 derivatives p))
      (multiply reals
        (quarter reals)
        (square reals
          (add reals
            (d12 derivatives p)
            (d21 derivatives p)))))

SatisfiesHypotheses :
  {R : Set} ->
  CompleteOrderedRealField R ->
  (Point R -> Point R) ->
  Set
SatisfiesHypotheses reals function =
  Exists (PartialDerivativeData reals function)
    (\ derivatives ->
      AllPartialsPositive derivatives
      and
      QuadraticInequality derivatives)

Injective :
  {A B : Set} ->
  (A -> B) ->
  Set
Injective {A = A} function =
  (x y : A) ->
  function x == function y ->
  x == y

putnam-2018-b5 : Set1
putnam-2018-b5 =
  (R : Set) ->
  (reals : CompleteOrderedRealField R) ->
  (function : Point R -> Point R) ->
  SatisfiesHypotheses reals function ->
  Injective function
