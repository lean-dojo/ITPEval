-- Statement-only formalization of PutnamBench corpus artifact putnam_1970_b3:
-- a closed subset of the real plane confined to an open vertical strip has
-- a closed projection on the y-axis. This file contains no proof.

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

record Point (R : Set) : Set where
  constructor point
  field
    x-coordinate : R
    y-coordinate : R

open Point

RealSubset : Set -> Set1
RealSubset R =
  R -> Set

PlaneSubset : Set -> Set1
PlaneSubset R =
  Point R -> Set

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

StrictPositive :
  {R : Set} ->
  CompleteOrderedRealField R ->
  R ->
  Set
StrictPositive reals radius =
  StrictLess reals (zeroR reals) radius

OpenRealBall :
  {R : Set} ->
  CompleteOrderedRealField R ->
  R ->
  R ->
  R ->
  Set
OpenRealBall reals center radius x =
  StrictLess reals
    (subtract reals center radius)
    x
  and
  StrictLess reals
    x
    (add reals center radius)

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

OpenPlaneBall :
  {R : Set} ->
  CompleteOrderedRealField R ->
  Point R ->
  R ->
  Point R ->
  Set
OpenPlaneBall reals center radius p =
  StrictLess reals
    (squaredDistance reals center p)
    (square reals radius)

ClosedReal :
  {R : Set} ->
  CompleteOrderedRealField R ->
  RealSubset R ->
  Set
ClosedReal {R} reals S =
  (x : R) ->
  Not (S x) ->
  Exists R
    (\ radius ->
      StrictPositive reals radius
      and
      ((y : R) ->
        OpenRealBall reals x radius y ->
        Not (S y)))

ClosedPlane :
  {R : Set} ->
  CompleteOrderedRealField R ->
  PlaneSubset R ->
  Set
ClosedPlane {R} reals S =
  (p : Point R) ->
  Not (S p) ->
  Exists R
    (\ radius ->
      StrictPositive reals radius
      and
      ((q : Point R) ->
        OpenPlaneBall reals p radius q ->
        Not (S q)))

ProjectionOnYAxis :
  {R : Set} ->
  PlaneSubset R ->
  RealSubset R
ProjectionOnYAxis {R} S y =
  Exists R
    (\ x -> S (point x y))

module Putnam1970B3Statement
  {R : Set}
  (reals : CompleteOrderedRealField R) where

  proposition : Set1
  proposition =
    (S : PlaneSubset R) ->
    (a b : R) ->
    StrictLess reals a b ->
    ((p : Point R) ->
      S p ->
      StrictLess reals a (x-coordinate p)
      and
      StrictLess reals (x-coordinate p) b) ->
    ClosedPlane reals S ->
    ClosedReal reals (ProjectionOnYAxis S)

putnam-1970-b3 : Set1
putnam-1970-b3 =
  (R : Set) ->
  (reals : CompleteOrderedRealField R) ->
  Putnam1970B3Statement.proposition reals
