-- Statement-only formalization of PutnamBench corpus artifact putnam_2010_a3
-- (putnambench__agda__putnam_2010_a3): every bounded continuously
-- differentiable real function on the plane satisfying h = a h_x + b h_y is
-- identically zero. This file contains no proof.

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

record Plane (R : Set) : Set where
  constructor point
  field
    x-coordinate : R
    y-coordinate : R

open Plane

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

PlaneCloseTo :
  {R : Set} ->
  CompleteOrderedRealField R ->
  Plane R ->
  R ->
  Plane R ->
  Set
PlaneCloseTo reals center radius p =
  CloseTo reals
    (x-coordinate center)
    radius
    (x-coordinate p)
  and
  CloseTo reals
    (y-coordinate center)
    radius
    (y-coordinate p)

xDifferenceQuotient :
  {R : Set} ->
  CompleteOrderedRealField R ->
  (Plane R -> R) ->
  Plane R ->
  R ->
  R
xDifferenceQuotient reals h p x =
  divide reals
    (subtract reals
      (h (point x (y-coordinate p)))
      (h p))
    (subtract reals x (x-coordinate p))

yDifferenceQuotient :
  {R : Set} ->
  CompleteOrderedRealField R ->
  (Plane R -> R) ->
  Plane R ->
  R ->
  R
yDifferenceQuotient reals h p y =
  divide reals
    (subtract reals
      (h (point (x-coordinate p) y))
      (h p))
    (subtract reals y (y-coordinate p))

HasXPartialDerivativeAt :
  {R : Set} ->
  CompleteOrderedRealField R ->
  (Plane R -> R) ->
  Plane R ->
  R ->
  Set
HasXPartialDerivativeAt {R} reals h p derivative =
  (epsilon : R) ->
  Positive reals epsilon ->
  Exists R
    (\ delta ->
      Positive reals delta
      and
      ((x : R) ->
        CloseTo reals (x-coordinate p) delta x ->
        x != x-coordinate p ->
        CloseTo reals derivative epsilon
          (xDifferenceQuotient reals h p x)))

HasYPartialDerivativeAt :
  {R : Set} ->
  CompleteOrderedRealField R ->
  (Plane R -> R) ->
  Plane R ->
  R ->
  Set
HasYPartialDerivativeAt {R} reals h p derivative =
  (epsilon : R) ->
  Positive reals epsilon ->
  Exists R
    (\ delta ->
      Positive reals delta
      and
      ((y : R) ->
        CloseTo reals (y-coordinate p) delta y ->
        y != y-coordinate p ->
        CloseTo reals derivative epsilon
          (yDifferenceQuotient reals h p y)))

ContinuousAtOnPlane :
  {R : Set} ->
  CompleteOrderedRealField R ->
  (Plane R -> R) ->
  Plane R ->
  Set
ContinuousAtOnPlane {R} reals function center =
  (epsilon : R) ->
  Positive reals epsilon ->
  Exists R
    (\ delta ->
      Positive reals delta
      and
      ((p : Plane R) ->
        PlaneCloseTo reals center delta p ->
        CloseTo reals
          (function center)
          epsilon
          (function p)))

ContinuousOnPlane :
  {R : Set} ->
  CompleteOrderedRealField R ->
  (Plane R -> R) ->
  Set
ContinuousOnPlane {R} reals function =
  (p : Plane R) ->
  ContinuousAtOnPlane reals function p

ContinuousPartialsSolveEquation :
  {R : Set} ->
  CompleteOrderedRealField R ->
  (Plane R -> R) ->
  R ->
  R ->
  (Plane R -> R) ->
  (Plane R -> R) ->
  Set
ContinuousPartialsSolveEquation {R} reals h a b partialX partialY =
  ((p : Plane R) ->
    HasXPartialDerivativeAt reals h p (partialX p))
  and
  ((p : Plane R) ->
    HasYPartialDerivativeAt reals h p (partialY p))
  and
  ContinuousOnPlane reals partialX
  and
  ContinuousOnPlane reals partialY
  and
  ((p : Plane R) ->
    h p ==
      add reals
        (multiply reals a (partialX p))
        (multiply reals b (partialY p)))

HasContinuousPartialsAndEquation :
  {R : Set} ->
  CompleteOrderedRealField R ->
  (Plane R -> R) ->
  R ->
  R ->
  Set
HasContinuousPartialsAndEquation {R} reals h a b =
  Exists (Plane R -> R)
    (\ partialX ->
      Exists (Plane R -> R)
        (\ partialY ->
          ContinuousPartialsSolveEquation
            reals h a b partialX partialY))

BoundedBy :
  {R : Set} ->
  CompleteOrderedRealField R ->
  (Plane R -> R) ->
  R ->
  Set
BoundedBy {R} reals h M =
  (p : Plane R) ->
  lessOrEqual reals (negate reals M) (h p)
  and
  lessOrEqual reals (h p) M

putnam-2010-a3 : Set1
putnam-2010-a3 =
  (R : Set) ->
  (reals : CompleteOrderedRealField R) ->
  (h : Plane R -> R) ->
  (a b M : R) ->
  HasContinuousPartialsAndEquation reals h a b ->
  BoundedBy reals h M ->
  (p : Plane R) ->
  h p == zeroR reals
