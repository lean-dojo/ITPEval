-- Statement-only formalization of PutnamBench corpus artifact putnam_1968_a4:
-- the sum of squared distances between unordered pairs of n points on the
-- unit sphere in real three-space is at most n squared. This file contains no proof.

{-# OPTIONS --safe #-}

open import Agda.Builtin.Equality renaming (_≡_ to _==_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)

infix 4 _!=_
infixr 3 _and_
infixr 2 _or_

data Bottom : Set where

Not : Set -> Set
Not A = A -> Bottom

_!=_ : {A : Set} -> A -> A -> Set
x != y = Not (x == y)

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
          ((x : R) -> P x -> lessOrEqual x supremum)
          and
          ((upper : R) ->
            ((x : R) -> P x -> lessOrEqual x upper) ->
            lessOrEqual supremum upper))

open CompleteOrderedField

record Point3 (R : Set) : Set where
  constructor point3
  field
    x-coordinate : R
    y-coordinate : R
    z-coordinate : R

open Point3

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

squaredNorm :
  {R : Set} ->
  CompleteOrderedField R ->
  Point3 R ->
  R
squaredNorm reals point =
  add reals
    (add reals
      (square reals (x-coordinate point))
      (square reals (y-coordinate point)))
    (square reals (z-coordinate point))

squaredDistance :
  {R : Set} ->
  CompleteOrderedField R ->
  Point3 R ->
  Point3 R ->
  R
squaredDistance reals leftPoint rightPoint =
  add reals
    (add reals
      (square reals
        (subtract reals
          (x-coordinate leftPoint)
          (x-coordinate rightPoint)))
      (square reals
        (subtract reals
          (y-coordinate leftPoint)
          (y-coordinate rightPoint))))
    (square reals
      (subtract reals
        (z-coordinate leftPoint)
        (z-coordinate rightPoint)))

sumFin :
  {R : Set} ->
  CompleteOrderedField R ->
  {n : Nat} ->
  (Fin n -> R) ->
  R
sumFin reals {zero} term =
  zeroR reals
sumFin reals {suc n} term =
  add reals
    (term fzero)
    (sumFin reals (\ i -> term (fsuc i)))

unorderedPairSquaredDistanceSum :
  {R : Set} ->
  CompleteOrderedField R ->
  {n : Nat} ->
  (Fin n -> Point3 R) ->
  R
unorderedPairSquaredDistanceSum reals {zero} points =
  zeroR reals
unorderedPairSquaredDistanceSum reals {suc n} points =
  add reals
    (sumFin reals
      (\ j ->
        squaredDistance reals
          (points fzero)
          (points (fsuc j))))
    (unorderedPairSquaredDistanceSum reals
      (\ i -> points (fsuc i)))

module Putnam1968A4Statement
  {R : Set}
  (reals : CompleteOrderedField R) where

  proposition : Set
  proposition =
    (n : Nat) ->
    (points : Fin n -> Point3 R) ->
    ((i : Fin n) ->
      squaredNorm reals (points i) == oneR reals) ->
    lessOrEqual reals
      (unorderedPairSquaredDistanceSum reals points)
      (square reals (fromNat reals n))

putnam-1968-a4 : Set1
putnam-1968-a4 =
  (R : Set) ->
  (reals : CompleteOrderedField R) ->
  Putnam1968A4Statement.proposition reals
