-- Statement-only formalization of PutnamBench corpus artifact putnam_2003_b5
-- (putnambench__agda__putnam_2003_b5): existence of a triangle whose side
-- lengths are the distances from an interior point to three equally spaced
-- unit-circle points, with area depending only on the point's radius.
-- This file contains no proof.

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

record StandardSquareRoot
  {R : Set}
  (reals : CompleteOrderedRealField R) :
  Set1 where

  field
    squareRoot : R -> R

    square-root-nonnegative :
      (x : R) ->
      lessOrEqual reals (zeroR reals) (squareRoot x)
    square-root-square :
      (x : R) ->
      lessOrEqual reals (zeroR reals) x ->
      square reals (squareRoot x) == x
    square-root-nonpositive :
      (x : R) ->
      lessOrEqual reals x (zeroR reals) ->
      squareRoot x == zeroR reals
    square-root-unique :
      (x y : R) ->
      lessOrEqual reals (zeroR reals) y ->
      square reals y == x ->
      squareRoot x == y

open StandardSquareRoot

record Point (R : Set) : Set where
  constructor point
  field
    x-coordinate : R
    y-coordinate : R

open Point

origin :
  {R : Set} ->
  CompleteOrderedRealField R ->
  Point R
origin reals =
  point (zeroR reals) (zeroR reals)

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
  (reals : CompleteOrderedRealField R) ->
  StandardSquareRoot reals ->
  Point R ->
  Point R ->
  R
distance reals roots p q =
  squareRoot roots (squaredDistance reals p q)

two :
  {R : Set} ->
  CompleteOrderedRealField R ->
  R
two reals =
  fromNat reals (suc (suc zero))

half :
  {R : Set} ->
  CompleteOrderedRealField R ->
  R
half reals =
  inverse reals (two reals)

doubleSignedArea :
  {R : Set} ->
  CompleteOrderedRealField R ->
  Point R ->
  Point R ->
  Point R ->
  R
doubleSignedArea reals a b c =
  subtract reals
    (multiply reals
      (subtract reals (x-coordinate b) (x-coordinate a))
      (subtract reals (y-coordinate c) (y-coordinate a)))
    (multiply reals
      (subtract reals (y-coordinate b) (y-coordinate a))
      (subtract reals (x-coordinate c) (x-coordinate a)))

triangleArea :
  {R : Set} ->
  (reals : CompleteOrderedRealField R) ->
  StandardSquareRoot reals ->
  Point R ->
  Point R ->
  Point R ->
  R
triangleArea reals roots a b c =
  multiply reals
    (half reals)
    (squareRoot roots
      (square reals (doubleSignedArea reals a b c)))

module Putnam2003B5Statement
  {R : Set}
  (reals : CompleteOrderedRealField R)
  (roots : StandardSquareRoot reals) where

  EquilateralUnitCircleConfiguration :
    Point R ->
    Point R ->
    Point R ->
    Set
  EquilateralUnitCircleConfiguration A B C =
    distance reals roots (origin reals) A == oneR reals
    and
    distance reals roots (origin reals) B == oneR reals
    and
    distance reals roots (origin reals) C == oneR reals
    and
    distance reals roots A B == distance reals roots A C
    and
    distance reals roots A B == distance reals roots B C
    and
    distance reals roots A B != zeroR reals

  HasRequiredTriangle :
    Point R ->
    Point R ->
    Point R ->
    (R -> R) ->
    Point R ->
    Set
  HasRequiredTriangle A B C f P =
    Exists (Point R)
      (\ X ->
        Exists (Point R)
          (\ Y ->
            Exists (Point R)
              (\ Z ->
                distance reals roots X Y == distance reals roots P A
                and
                distance reals roots Y Z == distance reals roots P B
                and
                distance reals roots X Z == distance reals roots P C
                and
                triangleArea reals roots X Y Z ==
                  f (distance reals roots (origin reals) P))))

  proposition : Set
  proposition =
    (A B C : Point R) ->
    EquilateralUnitCircleConfiguration A B C ->
    Exists (R -> R)
      (\ f ->
        (P : Point R) ->
        StrictLess reals
          (distance reals roots (origin reals) P)
          (oneR reals) ->
        HasRequiredTriangle A B C f P)

putnam-2003-b5 : Set1
putnam-2003-b5 =
  (R : Set) ->
  (reals : CompleteOrderedRealField R) ->
  (roots : StandardSquareRoot reals) ->
  Putnam2003B5Statement.proposition reals roots
