-- Statement-only formalization of thousand-theorems corpus artifact Q11518
-- (thousand-theorems__agda__Q11518), "Pythagorean theorem": in a real
-- Euclidean affine space, the squared-distance identity holds exactly when
-- the angle at the middle point is pi divided by two. This file contains no proof.

{-# OPTIONS --safe #-}

module Q11518_pythagorean_theorem where

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

record Iff (A B : Set) : Set where
  constructor equivalence
  field
    forward  : A -> B
    backward : B -> A

record CompleteOrderedField (R : Set) : Set1 where
  field
    zeroR oneR : R
    addR multiplyR : R -> R -> R
    negateR inverseR : R -> R
    lessOrEqualR : R -> R -> Set
    fromNatR : Nat -> R

    one-not-zeroR :
      oneR != zeroR

    add-commutativeR :
      (x y : R) ->
      addR x y == addR y x
    add-associativeR :
      (x y z : R) ->
      addR (addR x y) z == addR x (addR y z)
    add-zeroR :
      (x : R) ->
      addR x zeroR == x
    add-inverseR :
      (x : R) ->
      addR x (negateR x) == zeroR

    multiply-commutativeR :
      (x y : R) ->
      multiplyR x y == multiplyR y x
    multiply-associativeR :
      (x y z : R) ->
      multiplyR (multiplyR x y) z ==
      multiplyR x (multiplyR y z)
    multiply-oneR :
      (x : R) ->
      multiplyR x oneR == x
    multiply-zeroR :
      (x : R) ->
      multiplyR x zeroR == zeroR
    distributeR :
      (x y z : R) ->
      multiplyR x (addR y z) ==
      addR (multiplyR x y) (multiplyR x z)
    inverse-zeroR :
      inverseR zeroR == zeroR
    multiply-inverseR :
      (x : R) ->
      x != zeroR ->
      multiplyR x (inverseR x) == oneR

    order-reflexiveR :
      (x : R) ->
      lessOrEqualR x x
    order-transitiveR :
      (x y z : R) ->
      lessOrEqualR x y ->
      lessOrEqualR y z ->
      lessOrEqualR x z
    order-antisymmetricR :
      (x y : R) ->
      lessOrEqualR x y ->
      lessOrEqualR y x ->
      x == y
    order-totalR :
      (x y : R) ->
      lessOrEqualR x y or lessOrEqualR y x
    add-orderR :
      (x y z : R) ->
      lessOrEqualR x y ->
      lessOrEqualR (addR z x) (addR z y)
    multiply-nonnegativeR :
      (x y : R) ->
      lessOrEqualR zeroR x ->
      lessOrEqualR zeroR y ->
      lessOrEqualR zeroR (multiplyR x y)
    zero-less-than-oneR :
      lessOrEqualR zeroR oneR and oneR != zeroR

    fromNat-zeroR :
      fromNatR zero == zeroR
    fromNat-successorR :
      (n : Nat) ->
      fromNatR (suc n) == addR (fromNatR n) oneR

    archimedeanR :
      (x : R) ->
      Exists Nat (\ n -> lessOrEqualR x (fromNatR n))
    least-upper-boundR :
      (P : R -> Set) ->
      Exists R P ->
      Exists R
        (\ upper ->
          (x : R) ->
          P x ->
          lessOrEqualR x upper) ->
      Exists R
        (\ supremum ->
          ((x : R) ->
            P x ->
            lessOrEqualR x supremum)
          and
          ((upper : R) ->
            ((x : R) ->
              P x ->
              lessOrEqualR x upper) ->
            lessOrEqualR supremum upper))

open CompleteOrderedField

divide :
  {R : Set} ->
  CompleteOrderedField R ->
  R ->
  R ->
  R
divide reals x y =
  multiplyR reals x (inverseR reals y)

StrictLess :
  {R : Set} ->
  CompleteOrderedField R ->
  R ->
  R ->
  Set
StrictLess reals x y =
  lessOrEqualR reals x y and x != y

twoN : Nat
twoN =
  suc (suc zero)

ValidCosineInput :
  {R : Set} ->
  CompleteOrderedField R ->
  R ->
  Set
ValidCosineInput reals x =
  lessOrEqualR reals (negateR reals (oneR reals)) x
  and
  lessOrEqualR reals x (oneR reals)

record StandardRealTrigonometry
  {R : Set}
  (reals : CompleteOrderedField R) :
  Set1 where

  field
    sine cosine arccosine : R -> R
    pi : R

    sine-zero :
      sine (zeroR reals) == zeroR reals
    cosine-zero :
      cosine (zeroR reals) == oneR reals
    sine-addition :
      (x y : R) ->
      sine (addR reals x y) ==
      addR reals
        (multiplyR reals (sine x) (cosine y))
        (multiplyR reals (cosine x) (sine y))
    cosine-addition :
      (x y : R) ->
      cosine (addR reals x y) ==
      addR reals
        (multiplyR reals (cosine x) (cosine y))
        (negateR reals
          (multiplyR reals (sine x) (sine y)))
    sine-negate :
      (x : R) ->
      sine (negateR reals x) == negateR reals (sine x)
    cosine-negate :
      (x : R) ->
      cosine (negateR reals x) == cosine x
    sine-square-add-cosine-square :
      (x : R) ->
      addR reals
        (multiplyR reals (sine x) (sine x))
        (multiplyR reals (cosine x) (cosine x))
      ==
      oneR reals

    pi-positive :
      StrictLess reals (zeroR reals) pi
    sine-pi :
      sine pi == zeroR reals
    cosine-pi :
      cosine pi == negateR reals (oneR reals)
    sine-positive-before-pi :
      (x : R) ->
      StrictLess reals (zeroR reals) x ->
      StrictLess reals x pi ->
      StrictLess reals (zeroR reals) (sine x)

    arccosine-range :
      (x : R) ->
      ValidCosineInput reals x ->
      lessOrEqualR reals (zeroR reals) (arccosine x)
      and
      lessOrEqualR reals (arccosine x) pi
    cosine-arccosine :
      (x : R) ->
      ValidCosineInput reals x ->
      cosine (arccosine x) == x
    arccosine-cosine :
      (x : R) ->
      lessOrEqualR reals (zeroR reals) x ->
      lessOrEqualR reals x pi ->
      arccosine (cosine x) == x

open StandardRealTrigonometry

record RealInnerProductSpace
  {R : Set}
  (reals : CompleteOrderedField R)
  (V : Set) :
  Set1 where

  field
    zeroV : V
    addV : V -> V -> V
    negateV : V -> V
    scaleV : R -> V -> V

    addV-commutative :
      (u v : V) ->
      addV u v == addV v u
    addV-associative :
      (u v w : V) ->
      addV (addV u v) w == addV u (addV v w)
    addV-zero :
      (v : V) ->
      addV v zeroV == v
    addV-inverse :
      (v : V) ->
      addV v (negateV v) == zeroV

    scale-addV :
      (a : R) ->
      (u v : V) ->
      scaleV a (addV u v) ==
      addV (scaleV a u) (scaleV a v)
    add-scaleV :
      (a b : R) ->
      (v : V) ->
      scaleV (addR reals a b) v ==
      addV (scaleV a v) (scaleV b v)
    multiply-scaleV :
      (a b : R) ->
      (v : V) ->
      scaleV (multiplyR reals a b) v ==
      scaleV a (scaleV b v)
    one-scaleV :
      (v : V) ->
      scaleV (oneR reals) v == v

    inner : V -> V -> R
    inner-add-left :
      (u v w : V) ->
      inner (addV u v) w ==
      addR reals (inner u w) (inner v w)
    inner-scale-left :
      (a : R) ->
      (u v : V) ->
      inner (scaleV a u) v ==
      multiplyR reals a (inner u v)
    inner-symmetric :
      (u v : V) ->
      inner u v == inner v u
    inner-nonnegative :
      (v : V) ->
      lessOrEqualR reals (zeroR reals) (inner v v)
    inner-definite :
      (v : V) ->
      inner v v == zeroR reals ->
      v == zeroV

    norm : V -> R
    norm-nonnegative :
      (v : V) ->
      lessOrEqualR reals (zeroR reals) (norm v)
    norm-square :
      (v : V) ->
      multiplyR reals (norm v) (norm v) == inner v v
    norm-zero :
      (v : V) ->
      norm v == zeroR reals ->
      v == zeroV
    norm-negate :
      (v : V) ->
      norm (negateV v) == norm v

open RealInnerProductSpace

record AffineTorsor
  {R V : Set}
  {reals : CompleteOrderedField R}
  (space : RealInnerProductSpace reals V)
  (P : Set) :
  Set1 where

  field
    vadd : V -> P -> P
    vsub : P -> P -> V

    zero-vadd :
      (p : P) ->
      vadd (zeroV space) p == p
    add-vadd :
      (u v : V) ->
      (p : P) ->
      vadd (addV space u v) p ==
      vadd u (vadd v p)
    vadd-vsub :
      (p q : P) ->
      vadd (vsub p q) q == p
    vsub-vadd :
      (v : V) ->
      (p : P) ->
      vsub (vadd v p) p == v

open AffineTorsor

vectorAngle :
  {R V : Set} ->
  {reals : CompleteOrderedField R} ->
  StandardRealTrigonometry reals ->
  RealInnerProductSpace reals V ->
  V ->
  V ->
  R
vectorAngle {reals = reals} trigonometry space u v =
  arccosine trigonometry
    (divide reals
      (inner space u v)
      (multiplyR reals (norm space u) (norm space v)))

halfPi :
  {R : Set} ->
  {reals : CompleteOrderedField R} ->
  StandardRealTrigonometry reals ->
  R
halfPi {reals = reals} trigonometry =
  divide reals
    (pi trigonometry)
    (fromNatR reals twoN)

distance :
  {R V P : Set} ->
  {reals : CompleteOrderedField R} ->
  {space : RealInnerProductSpace reals V} ->
  AffineTorsor space P ->
  P ->
  P ->
  R
distance {space = space} affine p q =
  norm space (vsub affine p q)

angleAt :
  {R V P : Set} ->
  {reals : CompleteOrderedField R} ->
  StandardRealTrigonometry reals ->
  {space : RealInnerProductSpace reals V} ->
  AffineTorsor space P ->
  P ->
  P ->
  P ->
  R
angleAt trigonometry {space = space} affine p q r =
  vectorAngle trigonometry space
    (vsub affine p q)
    (vsub affine r q)

module PythagoreanTheoremStatement
  {R V P : Set}
  (reals : CompleteOrderedField R)
  (trigonometry : StandardRealTrigonometry reals)
  (space : RealInnerProductSpace reals V)
  (affine : AffineTorsor space P) where

  squaredDistanceIdentity :
    P ->
    P ->
    P ->
    Set
  squaredDistanceIdentity p1 p2 p3 =
    multiplyR reals
      (distance affine p1 p3)
      (distance affine p1 p3)
    ==
    addR reals
      (multiplyR reals
        (distance affine p1 p2)
        (distance affine p1 p2))
      (multiplyR reals
        (distance affine p3 p2)
        (distance affine p3 p2))

  rightAngleAtMiddle :
    P ->
    P ->
    P ->
    Set
  rightAngleAtMiddle p1 p2 p3 =
    angleAt trigonometry affine p1 p2 p3 ==
    halfPi trigonometry

  proposition : Set
  proposition =
    (p1 p2 p3 : P) ->
    Iff
      (squaredDistanceIdentity p1 p2 p3)
      (rightAngleAtMiddle p1 p2 p3)

pythagorean-theorem : Set1
pythagorean-theorem =
  (R V P : Set) ->
  (reals : CompleteOrderedField R) ->
  (trigonometry : StandardRealTrigonometry reals) ->
  (space : RealInnerProductSpace reals V) ->
  (affine : AffineTorsor space P) ->
  PythagoreanTheoremStatement.proposition
    reals
    trigonometry
    space
    affine
