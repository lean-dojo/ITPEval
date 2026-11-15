-- Statement-only formalization of PutnamBench corpus artifact putnam_1972_b5:
-- a non-coplanar quadrilateral in real Euclidean three-space with two pairs
-- of equal opposite angles has equal corresponding opposite side lengths.
-- This file contains no proof.

{-# OPTIONS --safe #-}

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

record Vector3 (R : Set) : Set where
  constructor vector3
  field
    x-coordinate : R
    y-coordinate : R
    z-coordinate : R

open Vector3

zeroVector :
  {R : Set} ->
  CompleteOrderedField R ->
  Vector3 R
zeroVector reals =
  vector3 (zeroR reals) (zeroR reals) (zeroR reals)

subtractR :
  {R : Set} ->
  CompleteOrderedField R ->
  R ->
  R ->
  R
subtractR reals x y =
  add reals x (negate reals y)

subtractVector :
  {R : Set} ->
  CompleteOrderedField R ->
  Vector3 R ->
  Vector3 R ->
  Vector3 R
subtractVector reals u v =
  vector3
    (subtractR reals (x-coordinate u) (x-coordinate v))
    (subtractR reals (y-coordinate u) (y-coordinate v))
    (subtractR reals (z-coordinate u) (z-coordinate v))

dot :
  {R : Set} ->
  CompleteOrderedField R ->
  Vector3 R ->
  Vector3 R ->
  R
dot reals u v =
  add reals
    (add reals
      (multiply reals (x-coordinate u) (x-coordinate v))
      (multiply reals (y-coordinate u) (y-coordinate v)))
    (multiply reals (z-coordinate u) (z-coordinate v))

determinant3 :
  {R : Set} ->
  CompleteOrderedField R ->
  Vector3 R ->
  Vector3 R ->
  Vector3 R ->
  R
determinant3 reals u v w =
  add reals
    (subtractR reals
      (multiply reals
        (x-coordinate u)
        (subtractR reals
          (multiply reals (y-coordinate v) (z-coordinate w))
          (multiply reals (z-coordinate v) (y-coordinate w))))
      (multiply reals
        (y-coordinate u)
        (subtractR reals
          (multiply reals (x-coordinate v) (z-coordinate w))
          (multiply reals (z-coordinate v) (x-coordinate w)))))
    (multiply reals
      (z-coordinate u)
      (subtractR reals
        (multiply reals (x-coordinate v) (y-coordinate w))
        (multiply reals (y-coordinate v) (x-coordinate w))))

record EuclideanNorm3
  {R : Set}
  (reals : CompleteOrderedField R) :
  Set1 where

  field
    norm : Vector3 R -> R
    norm-nonnegative :
      (v : Vector3 R) ->
      lessOrEqual reals (zeroR reals) (norm v)
    norm-square :
      (v : Vector3 R) ->
      multiply reals (norm v) (norm v) == dot reals v v
    norm-zero-vector :
      norm (zeroVector reals) == zeroR reals
    norm-definite :
      (v : Vector3 R) ->
      norm v == zeroR reals ->
      v == zeroVector reals

open EuclideanNorm3

distance :
  {R : Set} ->
  {reals : CompleteOrderedField R} ->
  EuclideanNorm3 reals ->
  Vector3 R ->
  Vector3 R ->
  R
distance {reals = reals} euclidean p q =
  norm euclidean (subtractVector reals p q)

normalizedDot :
  {R : Set} ->
  (reals : CompleteOrderedField R) ->
  EuclideanNorm3 reals ->
  Vector3 R ->
  Vector3 R ->
  R
normalizedDot reals euclidean u v =
  multiply reals
    (dot reals u v)
    (inverse reals
      (multiply reals (norm euclidean u) (norm euclidean v)))

angleCosineAt :
  {R : Set} ->
  (reals : CompleteOrderedField R) ->
  EuclideanNorm3 reals ->
  Vector3 R ->
  Vector3 R ->
  Vector3 R ->
  R
angleCosineAt reals euclidean a b c =
  normalizedDot reals euclidean
    (subtractVector reals a b)
    (subtractVector reals c b)

Noncoplanar :
  {R : Set} ->
  CompleteOrderedField R ->
  Vector3 R ->
  Vector3 R ->
  Vector3 R ->
  Vector3 R ->
  Set
Noncoplanar reals a b c d =
  determinant3 reals
    (subtractVector reals b a)
    (subtractVector reals c a)
    (subtractVector reals d a)
  !=
  zeroR reals

module Putnam1972B5Statement
  {R : Set}
  (reals : CompleteOrderedField R)
  (euclidean : EuclideanNorm3 reals) where

  proposition : Set
  proposition =
    (a b c d : Vector3 R) ->
    Noncoplanar reals a b c d ->
    (angleCosineAt reals euclidean a b c ==
       angleCosineAt reals euclidean c d a
    and
     angleCosineAt reals euclidean b c d ==
       angleCosineAt reals euclidean d a b) ->
    distance euclidean a b == distance euclidean c d
    and
    distance euclidean b c == distance euclidean d a

putnam-1972-b5 : Set1
putnam-1972-b5 =
  (R : Set) ->
  (reals : CompleteOrderedField R) ->
  (euclidean : EuclideanNorm3 reals) ->
  Putnam1972B5Statement.proposition reals euclidean
