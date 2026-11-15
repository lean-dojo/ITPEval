-- Statement-only formalization of Thousand Theorems corpus artifact Q4971339
-- (thousand-theorems__agda__Q4971339), "British flag theorem": in a real
-- Euclidean affine space, a parallelogram with a right angle has equal sums
-- of squared distances from any point to opposite vertices. This file contains no proof.

{-# OPTIONS --safe #-}

module Q4971339_british_flag_theorem where

open import Agda.Builtin.Equality renaming (_≡_ to _==_)
open import Agda.Builtin.Nat using (Nat; zero; suc)

infix 4 _!=_
infixr 3 _and_

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

data Either (A B : Set) : Set where
  left  : A -> Either A B
  right : B -> Either A B

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
      Either (lessOrEqualR x y) (lessOrEqualR y x)
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
      (lessOrEqualR zeroR oneR) and (oneR != zeroR)

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

record RealInnerProductAngleSpace
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

    pi halfPi : R
    vectorAngle : V -> V -> R

    half-pi-definition :
      halfPi ==
      multiplyR reals
        pi
        (inverseR reals (fromNatR reals (suc (suc zero))))
    half-pi-doubles :
      addR reals halfPi halfPi == pi
    vector-angle-symmetric :
      (u v : V) ->
      vectorAngle u v == vectorAngle v u
    vector-angle-zero-left :
      (v : V) ->
      vectorAngle zeroV v == halfPi
    vector-angle-zero-right :
      (v : V) ->
      vectorAngle v zeroV == halfPi
    vector-angle-nonnegative :
      (u v : V) ->
      lessOrEqualR reals (zeroR reals) (vectorAngle u v)
    vector-angle-at-most-pi :
      (u v : V) ->
      lessOrEqualR reals (vectorAngle u v) pi
    right-angle-characterization :
      (u v : V) ->
      Iff
        (vectorAngle u v == halfPi)
        (inner u v == zeroR reals)

open RealInnerProductAngleSpace

record AffineTorsor
  {R V : Set}
  {reals : CompleteOrderedField R}
  (space : RealInnerProductAngleSpace reals V)
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
  {reals : CompleteOrderedField R} ->
  {space : RealInnerProductAngleSpace reals V} ->
  AffineTorsor space P ->
  P ->
  P ->
  R
distance {space = space} affine p q =
  norm space (vsub affine p q)

angleAt :
  {R V P : Set} ->
  {reals : CompleteOrderedField R} ->
  {space : RealInnerProductAngleSpace reals V} ->
  AffineTorsor space P ->
  P ->
  P ->
  P ->
  R
angleAt {space = space} affine b a d =
  vectorAngle space
    (vsub affine b a)
    (vsub affine d a)

twoR :
  {R : Set} ->
  CompleteOrderedField R ->
  R
twoR reals =
  fromNatR reals (suc (suc zero))

halfR :
  {R : Set} ->
  CompleteOrderedField R ->
  R
halfR reals =
  inverseR reals (twoR reals)

midpoint :
  {R V P : Set} ->
  {reals : CompleteOrderedField R} ->
  {space : RealInnerProductAngleSpace reals V} ->
  AffineTorsor space P ->
  P ->
  P ->
  P
midpoint {reals = reals} {space = space} affine p q =
  vadd affine
    (scaleV space (halfR reals) (vsub affine p q))
    q

squaredDistance :
  {R V P : Set} ->
  {reals : CompleteOrderedField R} ->
  {space : RealInnerProductAngleSpace reals V} ->
  AffineTorsor space P ->
  P ->
  P ->
  R
squaredDistance {reals = reals} affine p q =
  multiplyR reals
    (distance affine p q)
    (distance affine p q)

british-flag-theorem : Set1
british-flag-theorem =
  (R V P : Set) ->
  (reals : CompleteOrderedField R) ->
  (space : RealInnerProductAngleSpace reals V) ->
  (affine : AffineTorsor space P) ->
  (a b c d : P) ->
  midpoint affine a c == midpoint affine b d ->
  angleAt affine b a d == halfPi space ->
  (p : P) ->
  addR reals
    (squaredDistance affine p a)
    (squaredDistance affine p c)
  ==
  addR reals
    (squaredDistance affine p b)
    (squaredDistance affine p d)
