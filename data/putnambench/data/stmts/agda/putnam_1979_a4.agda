-- Statement-only formalization of PutnamBench corpus artifact putnam_1979_a4:
-- equal finite red and blue point sets in the real plane, with no three points
-- collinear, admit a perfect red-blue matching by pairwise disjoint closed
-- line segments. This file contains no proof.

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

data Fin : Nat -> Set where
  fzero : {n : Nat} -> Fin (suc n)
  fsuc  : {n : Nat} -> Fin n -> Fin (suc n)

record HasCardinality
  {A : Set}
  (member : A -> Set)
  (cardinality : Nat) :
  Set where

  field
    enumerate :
      Fin cardinality ->
      A
    enumerated-member :
      (index : Fin cardinality) ->
      member (enumerate index)
    enumeration-complete :
      (item : A) ->
      member item ->
      Exists (Fin cardinality)
        (\ index -> item == enumerate index)
    enumeration-injective :
      (left-index right-index : Fin cardinality) ->
      enumerate left-index == enumerate right-index ->
      left-index == right-index

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

record Point (R : Set) : Set where
  constructor point
  field
    x-coordinate : R
    y-coordinate : R

open Point

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

affinePoint :
  {R : Set} ->
  CompleteOrderedRealField R ->
  Point R ->
  Point R ->
  R ->
  Point R
affinePoint reals p q t =
  addPoint reals
    (scalePoint reals t p)
    (scalePoint reals
      (subtract reals (oneR reals) t)
      q)

InClosedUnitInterval :
  {R : Set} ->
  CompleteOrderedRealField R ->
  R ->
  Set
InClosedUnitInterval reals t =
  lessOrEqual reals (zeroR reals) t
  and
  lessOrEqual reals t (oneR reals)

ClosedSegment :
  {R : Set} ->
  CompleteOrderedRealField R ->
  Point R ->
  Point R ->
  Point R ->
  Set
ClosedSegment {R} reals p q x =
  Exists R
    (\ t ->
      InClosedUnitInterval reals t
      and
      affinePoint reals p q t == x)

crossProduct :
  {R : Set} ->
  CompleteOrderedRealField R ->
  Point R ->
  Point R ->
  Point R ->
  R
crossProduct reals p q s =
  subtract reals
    (multiply reals
      (subtract reals (x-coordinate q) (x-coordinate p))
      (subtract reals (y-coordinate s) (y-coordinate p)))
    (multiply reals
      (subtract reals (y-coordinate q) (y-coordinate p))
      (subtract reals (x-coordinate s) (x-coordinate p)))

Noncollinear :
  {R : Set} ->
  CompleteOrderedRealField R ->
  Point R ->
  Point R ->
  Point R ->
  Set
Noncollinear reals p q s =
  crossProduct reals p q s != zeroR reals

Subset :
  Set ->
  Set1
Subset A =
  A -> Set

InUnion :
  {A : Set} ->
  Subset A ->
  Subset A ->
  A ->
  Set
InUnion left-set right-set x =
  left-set x or right-set x

Disjoint :
  {A : Set} ->
  Subset A ->
  Subset A ->
  Set
Disjoint {A} left-set right-set =
  (x : A) ->
  Not (left-set x and right-set x)

NoThreeCollinear :
  {R : Set} ->
  CompleteOrderedRealField R ->
  Subset (Point R) ->
  Subset (Point R) ->
  Set
NoThreeCollinear {R} reals red blue =
  (p q s : Point R) ->
  InUnion red blue p ->
  InUnion red blue q ->
  InUnion red blue s ->
  p != q ->
  p != s ->
  q != s ->
  Noncollinear reals p q s

SegmentsIntersect :
  {R : Set} ->
  CompleteOrderedRealField R ->
  Point R ->
  Point R ->
  Point R ->
  Point R ->
  Set
SegmentsIntersect {R} reals p q u v =
  Exists (Point R)
    (\ x ->
      ClosedSegment reals p q x
      and
      ClosedSegment reals u v x)

record PerfectDisjointMatching
  {R : Set}
  (reals : CompleteOrderedRealField R)
  (red blue : Subset (Point R))
  (cardinality : Nat) :
  Set where

  field
    red-endpoint :
      Fin cardinality ->
      Point R
    blue-endpoint :
      Fin cardinality ->
      Point R

    red-membership :
      (index : Fin cardinality) ->
      red (red-endpoint index)
    blue-membership :
      (index : Fin cardinality) ->
      blue (blue-endpoint index)

    red-injective :
      (left-index right-index : Fin cardinality) ->
      red-endpoint left-index == red-endpoint right-index ->
      left-index == right-index
    blue-injective :
      (left-index right-index : Fin cardinality) ->
      blue-endpoint left-index == blue-endpoint right-index ->
      left-index == right-index

    pairwise-disjoint :
      (left-index right-index : Fin cardinality) ->
      left-index != right-index ->
      Not
        (SegmentsIntersect reals
          (red-endpoint left-index)
          (blue-endpoint left-index)
          (red-endpoint right-index)
          (blue-endpoint right-index))

module Putnam1979A4Statement
  {R : Set}
  (reals : CompleteOrderedRealField R) where

  Plane : Set
  Plane =
    Point R

  proposition : Set1
  proposition =
    (red blue : Subset Plane) ->
    (n : Nat) ->
    HasCardinality red n ->
    HasCardinality blue n ->
    Disjoint red blue ->
    NoThreeCollinear reals red blue ->
    PerfectDisjointMatching reals red blue n

putnam-1979-a4 : Set1
putnam-1979-a4 =
  (R : Set) ->
  (reals : CompleteOrderedRealField R) ->
  Putnam1979A4Statement.proposition reals
