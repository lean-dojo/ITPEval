-- Statement-only formalization of PutnamBench corpus artifact putnam_1998_b2
-- (putnambench__agda__putnam_1998_b2): the minimum perimeter of a triangle
-- joining (a,b), the x-axis, and the line y = x. This file contains no proof.

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
    negate inverse squareRoot : R -> R
    lessOrEqual : R -> R -> Set
    fromNat : Nat -> R
    supremum infimum : (R -> Set) -> R

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

    supremum-property :
      (P : R -> Set) ->
      Exists R P ->
      Exists R
        (\ upper ->
          (x : R) ->
          P x ->
          lessOrEqual x upper) ->
      ((x : R) ->
        P x ->
        lessOrEqual x (supremum P))
      and
      ((upper : R) ->
        ((x : R) ->
          P x ->
          lessOrEqual x upper) ->
        lessOrEqual (supremum P) upper)

    infimum-property :
      (P : R -> Set) ->
      Exists R P ->
      Exists R
        (\ lower ->
          (x : R) ->
          P x ->
          lessOrEqual lower x) ->
      ((x : R) ->
        P x ->
        lessOrEqual (infimum P) x)
      and
      ((lower : R) ->
        ((x : R) ->
          P x ->
          lessOrEqual lower x) ->
        lessOrEqual lower (infimum P))

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

record Point (R : Set) : Set where
  constructor point
  field
    x-coordinate : R
    y-coordinate : R

open Point

squaredDistance :
  {R : Set} ->
  CompleteOrderedRealField R ->
  Point R ->
  Point R ->
  R
squaredDistance reals p q =
  add reals
    (square reals
      (subtract reals (x-coordinate p) (x-coordinate q)))
    (square reals
      (subtract reals (y-coordinate p) (y-coordinate q)))

distance :
  {R : Set} ->
  CompleteOrderedRealField R ->
  Point R ->
  Point R ->
  R
distance reals p q =
  squareRoot reals (squaredDistance reals p q)

module Putnam1998B2Statement
  {R : Set}
  (reals : CompleteOrderedRealField R) where

  twoN : Nat
  twoN =
    suc (suc zero)

  two : R
  two =
    fromNat reals twoN

  fixedPoint : R -> R -> Point R
  fixedPoint a b =
    point a b

  axisPoint : R -> Point R
  axisPoint c =
    point c (zeroR reals)

  diagonalPoint : R -> Point R
  diagonalPoint x =
    point x x

  firstSide : R -> R -> R -> R
  firstSide a b c =
    distance reals (fixedPoint a b) (axisPoint c)

  secondSide : R -> R -> R
  secondSide c x =
    distance reals (axisPoint c) (diagonalPoint x)

  thirdSide : R -> R -> R -> R
  thirdSide a b x =
    distance reals (fixedPoint a b) (diagonalPoint x)

  perimeter : R -> R -> R -> R -> R
  perimeter a b c x =
    add reals
      (add reals
        (firstSide a b c)
        (secondSide c x))
      (thirdSide a b x)

  IsTriangle : R -> R -> R -> R -> Set
  IsTriangle a b c x =
    StrictLess reals
      (thirdSide a b x)
      (add reals
        (firstSide a b c)
        (secondSide c x))
    and
    StrictLess reals
      (secondSide c x)
      (add reals
        (firstSide a b c)
        (thirdSide a b x))
    and
    StrictLess reals
      (firstSide a b c)
      (add reals
        (secondSide c x)
        (thirdSide a b x))

  FeasiblePerimeter : R -> R -> R -> Set
  FeasiblePerimeter a b d =
    Exists R
      (\ c ->
        Exists R
          (\ x ->
            d == perimeter a b c x
            and
            IsTriangle a b c x))

  solution : R -> R -> R
  solution a b =
    squareRoot reals
      (add reals
        (multiply reals two (square reals a))
        (multiply reals two (square reals b)))

  proposition : Set
  proposition =
    (a b : R) ->
    StrictLess reals (zeroR reals) b
    and
    StrictLess reals b a ->
    infimum reals (FeasiblePerimeter a b) == solution a b

putnam-1998-b2 : Set1
putnam-1998-b2 =
  (R : Set) ->
  (reals : CompleteOrderedRealField R) ->
  Putnam1998B2Statement.proposition reals
