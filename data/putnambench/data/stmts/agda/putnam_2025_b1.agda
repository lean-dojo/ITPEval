-- Statement-only formalization of PutnamBench corpus artifact putnam_2025_b1
-- (putnambench__agda__putnam_2025_b1): a two-coloring of the real plane that
-- preserves the color of every monochromatic noncollinear triangle at its
-- circumcenter is constant. This file contains no proof.

{-# OPTIONS --safe #-}

module Putnam2025B1 where

open import Agda.Builtin.Bool using (Bool)
open import Agda.Builtin.Equality renaming (_≡_ to _==_)
open import Agda.Builtin.Nat using (Nat; zero; suc)

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
      (x y z : R) -> add (add x y) z == add x (add y z)
    add-zero :
      (x : R) -> add x zeroR == x
    add-inverse :
      (x : R) -> add x (negate x) == zeroR

    multiply-commutative :
      (x y : R) -> multiply x y == multiply y x
    multiply-associative :
      (x y z : R) ->
      multiply (multiply x y) z == multiply x (multiply y z)
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
      (n : Nat) -> fromNat (suc n) == add (fromNat n) oneR

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
          ((x : R) -> P x -> lessOrEqual x supremum)
          and
          ((upper : R) ->
            ((x : R) -> P x -> lessOrEqual x upper) ->
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

two :
  {R : Set} ->
  CompleteOrderedRealField R ->
  R
two reals =
  add reals (oneR reals) (oneR reals)

divide :
  {R : Set} ->
  CompleteOrderedRealField R ->
  R ->
  R ->
  R
divide reals numerator denominator =
  multiply reals numerator (inverse reals denominator)

record Point (R : Set) : Set where
  constructor point
  field
    x-coordinate : R
    y-coordinate : R

open Point

point-square :
  {R : Set} ->
  CompleteOrderedRealField R ->
  Point R ->
  R
point-square reals p =
  add reals
    (square reals (x-coordinate p))
    (square reals (y-coordinate p))

signed-area :
  {R : Set} ->
  CompleteOrderedRealField R ->
  Point R ->
  Point R ->
  Point R ->
  R
signed-area reals a b c =
  add reals
    (multiply reals
      (x-coordinate a)
      (subtract reals (y-coordinate b) (y-coordinate c)))
    (add reals
      (multiply reals
        (x-coordinate b)
        (subtract reals (y-coordinate c) (y-coordinate a)))
      (multiply reals
        (x-coordinate c)
        (subtract reals (y-coordinate a) (y-coordinate b))))

Noncollinear :
  {R : Set} ->
  CompleteOrderedRealField R ->
  Point R ->
  Point R ->
  Point R ->
  Set
Noncollinear reals a b c =
  signed-area reals a b c != zeroR reals

circumcenter-denominator :
  {R : Set} ->
  CompleteOrderedRealField R ->
  Point R ->
  Point R ->
  Point R ->
  R
circumcenter-denominator reals a b c =
  multiply reals (two reals) (signed-area reals a b c)

circumcenter-x-numerator :
  {R : Set} ->
  CompleteOrderedRealField R ->
  Point R ->
  Point R ->
  Point R ->
  R
circumcenter-x-numerator reals a b c =
  add reals
    (multiply reals
      (point-square reals a)
      (subtract reals (y-coordinate b) (y-coordinate c)))
    (add reals
      (multiply reals
        (point-square reals b)
        (subtract reals (y-coordinate c) (y-coordinate a)))
      (multiply reals
        (point-square reals c)
        (subtract reals (y-coordinate a) (y-coordinate b))))

circumcenter-y-numerator :
  {R : Set} ->
  CompleteOrderedRealField R ->
  Point R ->
  Point R ->
  Point R ->
  R
circumcenter-y-numerator reals a b c =
  add reals
    (multiply reals
      (point-square reals a)
      (subtract reals (x-coordinate c) (x-coordinate b)))
    (add reals
      (multiply reals
        (point-square reals b)
        (subtract reals (x-coordinate a) (x-coordinate c)))
      (multiply reals
        (point-square reals c)
        (subtract reals (x-coordinate b) (x-coordinate a))))

circumcenter :
  {R : Set} ->
  CompleteOrderedRealField R ->
  Point R ->
  Point R ->
  Point R ->
  Point R
circumcenter reals a b c =
  point
    (divide reals
      (circumcenter-x-numerator reals a b c)
      (circumcenter-denominator reals a b c))
    (divide reals
      (circumcenter-y-numerator reals a b c)
      (circumcenter-denominator reals a b c))

Monochromatic :
  {R : Set} ->
  (Point R -> Bool) ->
  Point R ->
  Point R ->
  Point R ->
  Set
Monochromatic color a b c =
  color a == color b and color a == color c

module Putnam2025B1Statement
  {R : Set}
  (reals : CompleteOrderedRealField R) where

  Plane : Set
  Plane =
    Point R

  proposition : Set
  proposition =
    (color : Plane -> Bool) ->
    ((a b c : Plane) ->
      Noncollinear reals a b c ->
      Monochromatic color a b c ->
      color (circumcenter reals a b c) == color a) ->
    Exists Bool
      (\ constant-color ->
        (p : Plane) ->
        color p == constant-color)

putnam-2025-b1 : Set1
putnam-2025-b1 =
  (R : Set) ->
  (reals : CompleteOrderedRealField R) ->
  Putnam2025B1Statement.proposition reals
