-- Statement-only formalization of PutnamBench corpus artifact putnam_2006_b1
-- (putnambench__agda__putnam_2006_b1): the real cubic x^3 + 3xy + y^3 = 1
-- has a unique equilateral three-point subset, of area 3 sqrt(3) / 2.
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

cube :
  {R : Set} ->
  CompleteOrderedRealField R ->
  R ->
  R
cube reals x =
  multiply reals (square reals x) x

divide :
  {R : Set} ->
  CompleteOrderedRealField R ->
  R ->
  R ->
  R
divide reals x y =
  multiply reals x (inverse reals y)

absolute :
  {R : Set} ->
  CompleteOrderedRealField R ->
  R ->
  R
absolute reals x =
  squareRoot reals (square reals x)

record Point (R : Set) : Set where
  constructor point
  field
    x-coordinate : R
    y-coordinate : R

open Point

PointEqual :
  {R : Set} ->
  Point R ->
  Point R ->
  Set
PointEqual p q =
  x-coordinate p == x-coordinate q
  and
  y-coordinate p == y-coordinate q

PointSet : Set -> Set1
PointSet R =
  Point R -> Set

SetEqual :
  {R : Set} ->
  PointSet R ->
  PointSet R ->
  Set
SetEqual {R} S T =
  (p : Point R) ->
  Iff (S p) (T p)

Subset :
  {R : Set} ->
  PointSet R ->
  PointSet R ->
  Set
Subset {R} S T =
  (p : Point R) ->
  S p ->
  T p

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

determinant :
  {R : Set} ->
  CompleteOrderedRealField R ->
  Point R ->
  Point R ->
  Point R ->
  R
determinant reals a b c =
  subtract reals
    (multiply reals
      (subtract reals (x-coordinate b) (x-coordinate a))
      (subtract reals (y-coordinate c) (y-coordinate a)))
    (multiply reals
      (subtract reals (y-coordinate b) (y-coordinate a))
      (subtract reals (x-coordinate c) (x-coordinate a)))

triangleArea :
  {R : Set} ->
  CompleteOrderedRealField R ->
  Point R ->
  Point R ->
  Point R ->
  R
triangleArea reals a b c =
  divide reals
    (absolute reals (determinant reals a b c))
    (fromNat reals 2)

record EnumeratesThree
  {R : Set}
  (S : PointSet R) :
  Set where

  field
    first-point second-point third-point : Point R

    first-member  : S first-point
    second-member : S second-point
    third-member  : S third-point

    first-second-distinct :
      Not (PointEqual first-point second-point)
    first-third-distinct :
      Not (PointEqual first-point third-point)
    second-third-distinct :
      Not (PointEqual second-point third-point)

    complete :
      (p : Point R) ->
      S p ->
      PointEqual p first-point
      or PointEqual p second-point
      or PointEqual p third-point

open EnumeratesThree

record Equilateral
  {R : Set}
  (reals : CompleteOrderedRealField R)
  (S : PointSet R) :
  Set where

  field
    three-points : EnumeratesThree S
    side-length  : R
    equal-distances :
      (p q : Point R) ->
      S p ->
      S q ->
      Not (PointEqual p q) ->
      distance reals p q == side-length

record HasArea
  {R : Set}
  (reals : CompleteOrderedRealField R)
  (S : PointSet R)
  (area : R) :
  Set where

  field
    enumeration : EnumeratesThree S
    area-equality :
      triangleArea reals
        (first-point enumeration)
        (second-point enumeration)
        (third-point enumeration)
      ==
      area

module Putnam2006B1Statement
  {R : Set}
  (reals : CompleteOrderedRealField R) where

  curve : PointSet R
  curve p =
    add reals
      (add reals
        (cube reals (x-coordinate p))
        (multiply reals
          (fromNat reals 3)
          (multiply reals
            (x-coordinate p)
            (y-coordinate p))))
      (cube reals (y-coordinate p))
    ==
    oneR reals

  Qualifies : PointSet R -> Set
  Qualifies S =
    Subset S curve
    and
    Equilateral reals S

  record UniqueEquilateralSet : Set1 where
    field
      set        : PointSet R
      property   : Qualifies set
      uniqueness :
        (other : PointSet R) ->
        Qualifies other ->
        SetEqual other set

  solution-area : R
  solution-area =
    divide reals
      (multiply reals
        (fromNat reals 3)
        (squareRoot reals (fromNat reals 3)))
      (fromNat reals 2)

  record AreaWitness : Set1 where
    field
      set         : PointSet R
      lies-on-curve : Subset set curve
      equilateral : Equilateral reals set
      has-area    : HasArea reals set solution-area

  record Conclusion : Set1 where
    field
      unique-equilateral-set : UniqueEquilateralSet
      area-witness           : AreaWitness

putnam-2006-b1 : Set1
putnam-2006-b1 =
  (R : Set) ->
  (reals : CompleteOrderedRealField R) ->
  Putnam2006B1Statement.Conclusion reals
