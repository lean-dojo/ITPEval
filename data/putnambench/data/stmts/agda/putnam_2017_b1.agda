-- Statement-only formalization of PutnamBench corpus artifact putnam_2017_b1:
-- two distinct real affine lines intersect exactly when every nonzero dilation
-- from every point off both lines maps a point of one line to the other.
-- This file contains no proof.

{-# OPTIONS --safe #-}

module Putnam2017B1 where

open import Agda.Builtin.Equality renaming (_≡_ to _==_)
open import Agda.Builtin.Nat using (Nat; zero; suc)

infix 4 _!=_
infixr 3 _and_

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

record Iff (A B : Set) : Set where
  constructor iff
  field
    forward  : A -> B
    backward : B -> A

record Exists (A : Set) (P : A -> Set) : Set where
  constructor witness
  field
    value    : A
    property : P value

data _or_ (A B : Set) : Set where
  left  : A -> A or B
  right : B -> A or B

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

record Point (R : Set) : Set where
  constructor point
  field
    x-coordinate : R
    y-coordinate : R

open Point

Line : Set -> Set1
Line R =
  Point R -> Set

PointEqual :
  {R : Set} ->
  Point R ->
  Point R ->
  Set
PointEqual p q =
  x-coordinate p == x-coordinate q
  and
  y-coordinate p == y-coordinate q

zeroPoint :
  {R : Set} ->
  CompleteOrderedRealField R ->
  Point R
zeroPoint reals =
  point (zeroR reals) (zeroR reals)

addPoint :
  {R : Set} ->
  CompleteOrderedRealField R ->
  Point R ->
  Point R ->
  Point R
addPoint reals p q =
  point
    (add reals (x-coordinate p) (x-coordinate q))
    (add reals (y-coordinate p) (y-coordinate q))

negatePoint :
  {R : Set} ->
  CompleteOrderedRealField R ->
  Point R ->
  Point R
negatePoint reals p =
  point
    (negate reals (x-coordinate p))
    (negate reals (y-coordinate p))

subtractPoint :
  {R : Set} ->
  CompleteOrderedRealField R ->
  Point R ->
  Point R ->
  Point R
subtractPoint reals p q =
  addPoint reals p (negatePoint reals q)

scalePoint :
  {R : Set} ->
  CompleteOrderedRealField R ->
  R ->
  Point R ->
  Point R
scalePoint reals scalar p =
  point
    (multiply reals scalar (x-coordinate p))
    (multiply reals scalar (y-coordinate p))

LineEqual :
  {R : Set} ->
  Line R ->
  Line R ->
  Set
LineEqual L K =
  (p : Point _) ->
  Iff (L p) (K p)

LineDistinct :
  {R : Set} ->
  Line R ->
  Line R ->
  Set
LineDistinct L K =
  Not (LineEqual L K)

AffineLine :
  {R : Set} ->
  CompleteOrderedRealField R ->
  Point R ->
  Point R ->
  Line R
AffineLine reals v w p =
  Exists _
    (\ t ->
      PointEqual p
        (addPoint reals v (scalePoint reals t w)))

IsLine :
  {R : Set} ->
  CompleteOrderedRealField R ->
  Line R ->
  Set
IsLine reals L =
  Exists _
    (\ v ->
      Exists _
        (\ w ->
          Not (PointEqual w (zeroPoint reals))
          and
          LineEqual L (AffineLine reals v w)))

LineFamilyEqual :
  {R : Set} ->
  (Line R -> Set) ->
  (Line R -> Set) ->
  Set1
LineFamilyEqual lines family =
  (L : Line _) ->
  Iff (lines L) (family L)

LinesIntersect :
  {R : Set} ->
  Line R ->
  Line R ->
  Set
LinesIntersect L1 L2 =
  Exists _
    (\ p ->
      L1 p and L2 p)

DilationCondition :
  {R : Set} ->
  CompleteOrderedRealField R ->
  Line R ->
  Line R ->
  Set
DilationCondition reals L1 L2 =
  (lambda : _) ->
  lambda != zeroR reals ->
  (P : Point _) ->
  (Not (L1 P) and Not (L2 P)) ->
  Exists _
    (\ A1 ->
      Exists _
        (\ A2 ->
          L1 A1
          and
          L2 A2
          and
          PointEqual
            (subtractPoint reals A2 P)
            (scalePoint reals lambda
              (subtractPoint reals A1 P))))

module Putnam2017B1Statement
  {R : Set}
  (reals : CompleteOrderedRealField R) where

  proposition : Set1
  proposition =
    (lines : Line R -> Set) ->
    (L1 L2 : Line R) ->
    (L1L2lines : lines L1 and lines L2) ->
    (L1L2distinct : LineDistinct L1 L2) ->
    (hlines : LineFamilyEqual lines (IsLine reals)) ->
    Iff
      (LinesIntersect L1 L2)
      (DilationCondition reals L1 L2)

putnam-2017-b1 : Set1
putnam-2017-b1 =
  (R : Set) ->
  (reals : CompleteOrderedRealField R) ->
  Putnam2017B1Statement.proposition reals
