-- Statement-only formalization of "Isosceles Triangle Theorem" from Hundred Theorems
-- item 065: in a real inner-product space, equal sides from the apex imply equal
-- base angles, including for degenerate triangles. This file contains no proof.

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
    multiply-inverse :
      (x : R) ->
      x != zero ->
      multiply x (inverse x) == one
    inverse-zero :
      inverse zero == zero

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

record RealInnerProductAngleSpace
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
    norm-zero :
      (v : V) -> norm v == zero -> v == zeroV
    norm-negate :
      (v : V) -> norm (negateV v) == norm v

    pi halfPi : R
    cosine : R -> R
    vectorAngle : V -> V -> R

    half-pi-doubles :
      add halfPi halfPi == pi
    cosine-half-pi :
      cosine halfPi == zero

    vector-angle-symmetric :
      (u v : V) -> vectorAngle u v == vectorAngle v u
    vector-angle-zero-left :
      (v : V) -> vectorAngle zeroV v == halfPi
    vector-angle-zero-right :
      (v : V) -> vectorAngle v zeroV == halfPi
    vector-angle-nonnegative :
      (u v : V) -> lessOrEqual zero (vectorAngle u v)
    vector-angle-at-most-pi :
      (u v : V) -> lessOrEqual (vectorAngle u v) pi
    vector-angle-cosine :
      (u v : V) ->
      inner u v ==
      multiply
        (multiply (norm u) (norm v))
        (cosine (vectorAngle u v))
    cosine-injective-on-angle-range :
      (x y : R) ->
      lessOrEqual zero x ->
      lessOrEqual x pi ->
      lessOrEqual zero y ->
      lessOrEqual y pi ->
      cosine x == cosine y ->
      x == y

open CompleteOrderedField
open RealInnerProductAngleSpace

subtractV :
  {R V : Set} ->
  {reals : CompleteOrderedField R} ->
  RealInnerProductAngleSpace reals V ->
  V ->
  V ->
  V
subtractV space u v =
  addV space u (negateV space v)

distance :
  {R V : Set} ->
  {reals : CompleteOrderedField R} ->
  RealInnerProductAngleSpace reals V ->
  V ->
  V ->
  R
distance space p q =
  norm space (subtractV space p q)

angleAt :
  {R V : Set} ->
  {reals : CompleteOrderedField R} ->
  RealInnerProductAngleSpace reals V ->
  V ->
  V ->
  V ->
  R
angleAt space a b c =
  vectorAngle space
    (subtractV space a b)
    (subtractV space c b)

module IsoscelesTriangleStatement
  {R V : Set}
  (reals : CompleteOrderedField R)
  (space : RealInnerProductAngleSpace reals V) where

  proposition : Set
  proposition =
    (a b c : V) ->
    distance space a c == distance space b c ->
    angleAt space b a c == angleAt space a b c

isosceles-triangle-theorem : Set1
isosceles-triangle-theorem =
  (R V : Set) ->
  (reals : CompleteOrderedField R) ->
  (space : RealInnerProductAngleSpace reals V) ->
  IsoscelesTriangleStatement.proposition reals space
