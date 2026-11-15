-- Statement-only formalization of PutnamBench corpus artifact putnam_2010_a5
-- (putnambench__agda__putnam_2010_a5): a group embedded in real three-space
-- whose cross products are group products or zero has all cross products zero.
-- This file contains no proof.

{-# OPTIONS --safe #-}

module Putnam2010A5 where

open import Agda.Builtin.Equality renaming (_≡_ to _==_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)
open import Agda.Primitive using (Level; lsuc; _⊔_)

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

record Exists
  {a p : Level}
  (A : Set a)
  (property : A -> Set p) :
  Set (a ⊔ p) where

  constructor witness
  field
    value     : A
    satisfies : property value

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

open CompleteOrderedRealField

subtract :
  {R : Set} ->
  CompleteOrderedRealField R ->
  R ->
  R ->
  R
subtract reals x y =
  add reals x (negate reals y)

record Vector3 (R : Set) : Set where
  constructor vector3
  field
    x-coordinate : R
    y-coordinate : R
    z-coordinate : R

open Vector3

zeroVector :
  {R : Set} ->
  CompleteOrderedRealField R ->
  Vector3 R
zeroVector reals =
  vector3
    (zeroR reals)
    (zeroR reals)
    (zeroR reals)

crossProduct :
  {R : Set} ->
  CompleteOrderedRealField R ->
  Vector3 R ->
  Vector3 R ->
  Vector3 R
crossProduct reals u v =
  vector3
    (subtract reals
      (multiply reals (y-coordinate u) (z-coordinate v))
      (multiply reals (z-coordinate u) (y-coordinate v)))
    (subtract reals
      (multiply reals (z-coordinate u) (x-coordinate v))
      (multiply reals (x-coordinate u) (z-coordinate v)))
    (subtract reals
      (multiply reals (x-coordinate u) (y-coordinate v))
      (multiply reals (y-coordinate u) (x-coordinate v)))

record Group
  {ell : Level}
  (G : Set ell) :
  Set ell where

  field
    identity       : G
    inverseG       : G -> G
    multiplyG      : G -> G -> G
    associative    : (x y z : G) ->
                     multiplyG (multiplyG x y) z ==
                     multiplyG x (multiplyG y z)
    identity-left  : (x : G) -> multiplyG identity x == x
    identity-right : (x : G) -> multiplyG x identity == x
    inverse-left   : (x : G) ->
                     multiplyG (inverseG x) x == identity
    inverse-right  : (x : G) ->
                     multiplyG x (inverseG x) == identity

open Group

record Injection
  {a b : Level}
  (A : Set a)
  (B : Set b) :
  Set (a ⊔ b) where

  field
    map : A -> B
    map-injective :
      (x y : A) ->
      map x == map y ->
      x == y

open Injection

putnam-2010-a5 :
  (ell : Level) ->
  Set (lsuc ell)
putnam-2010-a5 ell =
  (R : Set) ->
  (reals : CompleteOrderedRealField R) ->
  (G : Set ell) ->
  (group : Group G) ->
  (embedding : Injection G (Vector3 R)) ->
  ((a b : G) ->
    crossProduct reals (map embedding a) (map embedding b) ==
      map embedding (multiplyG group a b)
    or
    crossProduct reals (map embedding a) (map embedding b) ==
      zeroVector reals) ->
  (a b : G) ->
  crossProduct reals (map embedding a) (map embedding b) ==
    zeroVector reals
