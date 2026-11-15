-- Statement-only formalization of PutnamBench corpus artifact putnam_1975_b2:
-- countably many open slabs in three-dimensional Euclidean space, with positive
-- thicknesses whose series converges, do not cover the space. This file contains no proof.

{-# OPTIONS --safe #-}

open import Agda.Builtin.Equality renaming (_≡_ to _==_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)

infix 4 _!=_ _<=N_
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

data _<=N_ : Nat -> Nat -> Set where
  zero<=N   : {n : Nat} -> zero <=N n
  suc<=sucN : {m n : Nat} -> m <=N n -> suc m <=N suc n

record CompleteOrderedRealField (R : Set) : Set1 where
  field
    zeroR oneR : R
    add multiply : R -> R -> R
    negate inverse absoluteValue squareRoot : R -> R
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

    absolute-of-nonnegative :
      (x : R) ->
      lessOrEqual zeroR x ->
      absoluteValue x == x
    absolute-of-nonpositive :
      (x : R) ->
      lessOrEqual x zeroR ->
      absoluteValue x == negate x

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

StrictLess :
  {R : Set} ->
  CompleteOrderedRealField R ->
  R ->
  R ->
  Set
StrictLess reals x y =
  lessOrEqual reals x y and x != y

sumFirst :
  {R : Set} ->
  CompleteOrderedRealField R ->
  (Nat -> R) ->
  Nat ->
  R
sumFirst reals terms zero =
  zeroR reals
sumFirst reals terms (suc n) =
  add reals
    (sumFirst reals terms n)
    (terms n)

SequentialLimit :
  {R : Set} ->
  CompleteOrderedRealField R ->
  (Nat -> R) ->
  R ->
  Set
SequentialLimit {R} reals sequence limit =
  (epsilon : R) ->
  StrictLess reals (zeroR reals) epsilon ->
  Exists Nat
    (\ cutoff ->
      (n : Nat) ->
      cutoff <=N n ->
      StrictLess reals
        (absoluteValue reals
          (subtract reals (sequence n) limit))
        epsilon)

Convergent :
  {R : Set} ->
  CompleteOrderedRealField R ->
  (Nat -> R) ->
  Set
Convergent {R} reals sequence =
  Exists R (SequentialLimit reals sequence)

record Vector3 (R : Set) : Set where
  constructor vector3
  field
    firstCoordinate  : R
    secondCoordinate : R
    thirdCoordinate  : R

open Vector3

dotProduct :
  {R : Set} ->
  CompleteOrderedRealField R ->
  Vector3 R ->
  Vector3 R ->
  R
dotProduct reals u v =
  add reals
    (multiply reals
      (firstCoordinate u)
      (firstCoordinate v))
    (add reals
      (multiply reals
        (secondCoordinate u)
        (secondCoordinate v))
      (multiply reals
        (thirdCoordinate u)
        (thirdCoordinate v)))

euclideanNorm :
  {R : Set} ->
  CompleteOrderedRealField R ->
  Vector3 R ->
  R
euclideanNorm reals v =
  squareRoot reals (dotProduct reals v v)

InOpenSlab :
  {R : Set} ->
  CompleteOrderedRealField R ->
  Vector3 R ->
  R ->
  R ->
  Vector3 R ->
  Set
InOpenSlab reals normal offset thickness point =
  StrictLess reals
    offset
    (dotProduct reals normal point)
  and
  StrictLess reals
    (dotProduct reals normal point)
    (add reals offset thickness)

UnionCovers :
  {R : Set} ->
  CompleteOrderedRealField R ->
  (Nat -> Vector3 R) ->
  (Nat -> R) ->
  (Nat -> R) ->
  Set
UnionCovers {R} reals normals offsets thicknesses =
  (point : Vector3 R) ->
  Exists Nat
    (\ i ->
      InOpenSlab reals
        (normals i)
        (offsets i)
        (thicknesses i)
        point)

putnam-1975-b2 : Set1
putnam-1975-b2 =
  (R : Set) ->
  (reals : CompleteOrderedRealField R) ->
  (normals : Nat -> Vector3 R) ->
  (offsets : Nat -> R) ->
  (thicknesses : Nat -> R) ->
  ((i : Nat) ->
    euclideanNorm reals (normals i) == oneR reals) ->
  ((i : Nat) ->
    StrictLess reals (zeroR reals) (thicknesses i)) ->
  Convergent reals
    (\ i -> sumFirst reals thicknesses i) ->
  Not (UnionCovers reals normals offsets thicknesses)
