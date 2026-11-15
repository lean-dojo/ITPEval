-- Statement-only formalization of thousand-theorems corpus artifact Q2267175
-- (thousand-theorems__agda__Q2267175), "Tangent-secant theorem": in a real
-- Euclidean affine space, the squared distance from a point to a tangent point
-- of a sphere equals the product of its distances to two sphere points on a
-- secant line. This file contains no proof.

{-# OPTIONS --safe #-}

module Q2267175_tangent_secant_theorem where

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

record CompleteOrderedRealField (R : Set) : Set1 where
  field
    zeroR oneR : R
    addR multiplyR : R -> R -> R
    negateR inverseR squareRootR : R -> R
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

    square-root-nonnegativeR :
      (x : R) ->
      lessOrEqualR zeroR (squareRootR x)
    square-root-squareR :
      (x : R) ->
      lessOrEqualR zeroR x ->
      multiplyR (squareRootR x) (squareRootR x) == x
    square-root-nonpositiveR :
      (x : R) ->
      lessOrEqualR x zeroR ->
      squareRootR x == zeroR
    square-root-uniqueR :
      (x y : R) ->
      lessOrEqualR zeroR y ->
      multiplyR y y == x ->
      y == squareRootR x

open CompleteOrderedRealField

record RealInnerProductSpace
  {R : Set}
  (reals : CompleteOrderedRealField R)
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

open RealInnerProductSpace

record AffineTorsor
  {R V : Set}
  {reals : CompleteOrderedRealField R}
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

distance :
  {R V P : Set} ->
  {reals : CompleteOrderedRealField R} ->
  {space : RealInnerProductSpace reals V} ->
  AffineTorsor space P ->
  P ->
  P ->
  R
distance {reals = reals} {space = space} affine p q =
  squareRootR reals
    (inner space (vsub affine p q) (vsub affine p q))

OnAffineLine :
  {R V P : Set} ->
  {reals : CompleteOrderedRealField R} ->
  (space : RealInnerProductSpace reals V) ->
  AffineTorsor space P ->
  P ->
  P ->
  P ->
  Set
OnAffineLine {R} space affine a b x =
  Exists R
    (\ scalar ->
      x ==
      vadd affine
        (scaleV space scalar (vsub affine b a))
        a)

record Sphere {R P : Set} : Set where
  constructor sphere
  field
    center : P
    radius : R

open Sphere

OnSphere :
  {R V P : Set} ->
  {reals : CompleteOrderedRealField R} ->
  {space : RealInnerProductSpace reals V} ->
  AffineTorsor space P ->
  Sphere {R} {P} ->
  P ->
  Set
OnSphere affine s x =
  distance affine x (center s) == radius s

record IsTangentAt
  {R V P : Set}
  {reals : CompleteOrderedRealField R}
  (space : RealInnerProductSpace reals V)
  (affine : AffineTorsor space P)
  (s : Sphere {R} {P})
  (t p : P) :
  Set where

  field
    tangent-point-on-sphere :
      OnSphere affine s t
    tangent-point-on-line :
      OnAffineLine space affine p t t
    line-is-orthogonal-to-radius :
      (x : P) ->
      OnAffineLine space affine p t x ->
      inner space
        (vsub affine x t)
        (vsub affine t (center s))
      ==
      zeroR reals

tangent-secant-theorem : Set1
tangent-secant-theorem =
  (R V P : Set) ->
  (reals : CompleteOrderedRealField R) ->
  (space : RealInnerProductSpace reals V) ->
  (affine : AffineTorsor space P) ->
  (a b t p : P) ->
  (s : Sphere {R} {P}) ->
  OnSphere affine s a ->
  OnSphere affine s b ->
  OnAffineLine space affine a b p ->
  IsTangentAt space affine s t p ->
  multiplyR reals
    (distance affine p t)
    (distance affine p t)
  ==
  multiplyR reals
    (distance affine p a)
    (distance affine p b)
