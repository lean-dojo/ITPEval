-- Statement-only formalization of PutnamBench corpus artifact putnam_1964_b6:
-- the real unit disk cannot be partitioned into two disjoint congruent subsets.
-- This file contains no proof.

{-# OPTIONS --safe #-}

open import Agda.Primitive using (Level; _⊔_)
open import Agda.Builtin.Equality renaming (_≡_ to _==_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)

infix 4 _!=_
infixr 3 _and_
infixr 2 _or_

data Bottom : Set where

Not :
  {a : Level} ->
  Set a ->
  Set a
Not A =
  A -> Bottom

_!=_ :
  {a : Level} ->
  {A : Set a} ->
  A ->
  A ->
  Set a
x != y =
  Not (x == y)

record _and_
  {a b : Level}
  (A : Set a)
  (B : Set b) :
  Set (a ⊔ b) where

  constructor both
  field
    first  : A
    second : B

data _or_
  {a b : Level}
  (A : Set a)
  (B : Set b) :
  Set (a ⊔ b) where

  left  : A -> A or B
  right : B -> A or B

record Iff
  {a b : Level}
  (A : Set a)
  (B : Set b) :
  Set (a ⊔ b) where

  constructor iff
  field
    forward  : A -> B
    backward : B -> A

record Exists
  {a p : Level}
  (A : Set a)
  (P : A -> Set p) :
  Set (a ⊔ p) where

  constructor witness
  field
    value    : A
    property : P value

record CompleteOrderedField (R : Set) : Set1 where
  field
    zeroR oneR : R
    add multiply : R -> R -> R
    negate inverse : R -> R
    lessOrEqual : R -> R -> Set
    fromNat : Nat -> R

    one-not-zero :
      oneR != zeroR

    add-commutative :
      (x y : R) ->
      add x y == add y x
    add-associative :
      (x y z : R) ->
      add (add x y) z == add x (add y z)
    add-zero :
      (x : R) ->
      add x zeroR == x
    add-inverse :
      (x : R) ->
      add x (negate x) == zeroR

    multiply-commutative :
      (x y : R) ->
      multiply x y == multiply y x
    multiply-associative :
      (x y z : R) ->
      multiply (multiply x y) z == multiply x (multiply y z)
    multiply-one :
      (x : R) ->
      multiply x oneR == x
    multiply-zero :
      (x : R) ->
      multiply x zeroR == zeroR
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
      (x : R) ->
      lessOrEqual x x
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

open CompleteOrderedField

subtract :
  {R : Set} ->
  CompleteOrderedField R ->
  R ->
  R ->
  R
subtract reals x y =
  add reals x (negate reals y)

square :
  {R : Set} ->
  CompleteOrderedField R ->
  R ->
  R
square reals x =
  multiply reals x x

record Point (R : Set) : Set where
  constructor point
  field
    x-coordinate : R
    y-coordinate : R

open Point

SquaredDistance :
  {R : Set} ->
  CompleteOrderedField R ->
  Point R ->
  Point R ->
  R
SquaredDistance reals p q =
  add reals
    (square reals
      (subtract reals
        (x-coordinate p)
        (x-coordinate q)))
    (square reals
      (subtract reals
        (y-coordinate p)
        (y-coordinate q)))

module Putnam1964B6Statement
  {R : Set}
  (reals : CompleteOrderedField R) where

  Plane : Set
  Plane =
    Point R

  Subset : Set1
  Subset =
    Plane -> Set

  record SetEqual
    (A B : Subset) :
    Set where

    constructor same-set
    field
      membership :
        (p : Plane) ->
        Iff (A p) (B p)

  Empty : Subset
  Empty p =
    Bottom

  Intersection :
    Subset ->
    Subset ->
    Subset
  Intersection A B p =
    A p and B p

  Union :
    Subset ->
    Subset ->
    Subset
  Union A B p =
    A p or B p

  Image :
    (Plane -> Plane) ->
    Subset ->
    Subset
  Image f A q =
    Exists Plane
      (\ p ->
        A p and q == f p)

  origin : Plane
  origin =
    point (zeroR reals) (zeroR reals)

  UnitDisk : Subset
  UnitDisk p =
    lessOrEqual reals
      (SquaredDistance reals origin p)
      (oneR reals)

  DistancePreserving :
    (Plane -> Plane) ->
    Set
  DistancePreserving f =
    (p q : Plane) ->
    SquaredDistance reals p q ==
    SquaredDistance reals (f p) (f q)

  Congruent :
    Subset ->
    Subset ->
    Set
  Congruent A B =
    Exists (Plane -> Plane)
      (\ f ->
        SetEqual B (Image f A)
        and
        DistancePreserving f)

  Disjoint :
    Subset ->
    Subset ->
    Set
  Disjoint A B =
    SetEqual (Intersection A B) Empty

  proposition : Set1
  proposition =
    Not
      (Exists Subset
        (\ A ->
          Exists Subset
            (\ B ->
              Congruent A B
              and
              Disjoint A B
              and
              SetEqual (Union A B) UnitDisk)))

putnam-1964-b6 : Set1
putnam-1964-b6 =
  (R : Set) ->
  (reals : CompleteOrderedField R) ->
  Putnam1964B6Statement.proposition reals
