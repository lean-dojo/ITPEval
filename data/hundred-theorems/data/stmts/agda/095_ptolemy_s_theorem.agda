-- Statement-only formalization of Hundred Theorems corpus artifact
-- hundred-theorems__agda__095, "Ptolemy's Theorem": the products of the
-- diagonal and side lengths of a cyclic quadrilateral in cyclic order satisfy
-- Ptolemy's distance identity. This file contains no proof.

{-# OPTIONS --safe #-}

open import Agda.Builtin.Equality renaming (_≡_ to _==_)

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

data Natural : Set where
  natZero : Natural
  natSuc  : Natural -> Natural

record CompleteOrderedField (R : Set) : Set1 where
  field
    zero one : R
    add multiply : R -> R -> R
    negate inverse : R -> R
    lessOrEqual : R -> R -> Set
    fromNat : Natural -> R

    one-not-zero :
      one != zero

    add-commutative :
      (x y : R) -> add x y == add y x
    add-associative :
      (x y z : R) -> add (add x y) z == add x (add y z)
    add-zero :
      (x : R) -> add x zero == x
    add-inverse :
      (x : R) -> add x (negate x) == zero

    multiply-commutative :
      (x y : R) -> multiply x y == multiply y x
    multiply-associative :
      (x y z : R) ->
      multiply (multiply x y) z == multiply x (multiply y z)
    multiply-one :
      (x : R) -> multiply x one == x
    multiply-zero :
      (x : R) -> multiply x zero == zero
    distribute :
      (x y z : R) ->
      multiply x (add y z) ==
      add (multiply x y) (multiply x z)
    inverse-zero :
      inverse zero == zero
    multiply-inverse :
      (x : R) ->
      x != zero ->
      multiply x (inverse x) == one

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
      lessOrEqual zero x ->
      lessOrEqual zero y ->
      lessOrEqual zero (multiply x y)
    zero-less-than-one :
      lessOrEqual zero one and zero != one

    fromNat-zero :
      fromNat natZero == zero
    fromNat-successor :
      (n : Natural) -> fromNat (natSuc n) == add (fromNat n) one
    archimedean :
      (x : R) ->
      Exists Natural (\ n -> lessOrEqual x (fromNat n))
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

record RealInnerProductSpace
  {R : Set}
  (reals : CompleteOrderedField R)
  (V : Set) : Set1 where

  open CompleteOrderedField reals

  field
    zeroV : V
    addV : V -> V -> V
    negateV : V -> V
    scale : R -> V -> V

    addV-commutative :
      (u v : V) -> addV u v == addV v u
    addV-associative :
      (u v w : V) -> addV (addV u v) w == addV u (addV v w)
    addV-zero :
      (v : V) -> addV v zeroV == v
    addV-inverse :
      (v : V) -> addV v (negateV v) == zeroV

    scale-addV :
      (a : R) (u v : V) ->
      scale a (addV u v) == addV (scale a u) (scale a v)
    add-scale :
      (a b : R) (v : V) ->
      scale (add a b) v == addV (scale a v) (scale b v)
    multiply-scale :
      (a b : R) (v : V) ->
      scale (multiply a b) v == scale a (scale b v)
    one-scale :
      (v : V) -> scale one v == v

    inner : V -> V -> R
    inner-add-left :
      (u v w : V) ->
      inner (addV u v) w == add (inner u w) (inner v w)
    inner-scale-left :
      (a : R) (u v : V) ->
      inner (scale a u) v == multiply a (inner u v)
    inner-symmetric :
      (u v : V) -> inner u v == inner v u
    inner-nonnegative :
      (v : V) -> lessOrEqual zero (inner v v)
    inner-definite :
      (v : V) -> inner v v == zero -> v == zeroV

    norm : V -> R
    norm-nonnegative :
      (v : V) -> lessOrEqual zero (norm v)
    norm-square :
      (v : V) -> multiply (norm v) (norm v) == inner v v

open CompleteOrderedField
open RealInnerProductSpace

subtractR :
  {R : Set} ->
  CompleteOrderedField R ->
  R ->
  R ->
  R
subtractR reals x y =
  add reals x (negate reals y)

subtractV :
  {R V : Set} ->
  {reals : CompleteOrderedField R} ->
  RealInnerProductSpace reals V ->
  V ->
  V ->
  V
subtractV space u v =
  addV space u (negateV space v)

distance :
  {R V : Set} ->
  {reals : CompleteOrderedField R} ->
  RealInnerProductSpace reals V ->
  V ->
  V ->
  R
distance space p q =
  norm space (subtractV space p q)

Between :
  {R V : Set} ->
  (reals : CompleteOrderedField R) ->
  RealInnerProductSpace reals V ->
  V ->
  V ->
  V ->
  Set
Between {R} reals space p q x =
  Exists R
    (\ t ->
      lessOrEqual reals (zero reals) t
      and
      (lessOrEqual reals t (one reals)
      and
      x ==
        addV space
          (scale space t p)
          (scale space (subtractR reals (one reals) t) q)))

CosphericalFour :
  {R V : Set} ->
  (reals : CompleteOrderedField R) ->
  RealInnerProductSpace reals V ->
  V ->
  V ->
  V ->
  V ->
  Set
CosphericalFour {R} {V} reals space a b c d =
  Exists V
    (\ center ->
      Exists R
        (\ radius ->
          distance space center a == radius
          and
          distance space center b == radius
          and
          distance space center c == radius
          and
          distance space center d == radius))

CyclicQuadrilateralInOrder :
  {R V : Set} ->
  (reals : CompleteOrderedField R) ->
  RealInnerProductSpace reals V ->
  V ->
  V ->
  V ->
  V ->
  Set
CyclicQuadrilateralInOrder {V = V} reals space a b c d =
  CosphericalFour reals space a b c d
  and
  Exists V
    (\ p ->
      Between reals space a c p
      and
      Between reals space b d p)

module PtolemyStatement
  {R V : Set}
  (reals : CompleteOrderedField R)
  (space : RealInnerProductSpace reals V) where

  proposition : Set
  proposition =
    (a b c d : V) ->
    CyclicQuadrilateralInOrder reals space a b c d ->
    add reals
      (multiply reals
        (distance space a b)
        (distance space c d))
      (multiply reals
        (distance space b c)
        (distance space d a))
    ==
    multiply reals
      (distance space a c)
      (distance space b d)

ptolemys-theorem : Set1
ptolemys-theorem =
  (R V : Set) ->
  (reals : CompleteOrderedField R) ->
  (space : RealInnerProductSpace reals V) ->
  PtolemyStatement.proposition reals space
