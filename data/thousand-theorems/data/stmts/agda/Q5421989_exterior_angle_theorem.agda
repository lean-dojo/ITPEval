-- Statement-only formalization of thousand-theorems corpus artifact Q5421989
-- (thousand-theorems__agda__Q5421989), "Exterior angle theorem": in a real
-- inner-product affine space, strict extension of a triangle side makes the
-- canonical Euclidean exterior angle equal the sum of the two remote interior
-- angles. This file contains no proof.

{-# OPTIONS --safe #-}

module Q5421989_exterior_angle_theorem where

open import Agda.Builtin.Equality renaming (_≡_ to _==_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)

infix 4 _!=_
infix 4 _natLe_
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

data _natLe_ : Nat -> Nat -> Set where
  zero-le : {n : Nat} -> zero natLe n
  suc-le  : {m n : Nat} -> m natLe n -> suc m natLe suc n

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
    fromNat-additionR :
      (m n : Nat) ->
      fromNatR (m + n) == addR (fromNatR m) (fromNatR n)
    fromNat-injectiveR :
      (m n : Nat) ->
      fromNatR m == fromNatR n ->
      m == n

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

subtractR :
  {R : Set} ->
  CompleteOrderedField R ->
  R ->
  R ->
  R
subtractR reals x y =
  addR reals x (negateR reals y)

StrictLess :
  {R : Set} ->
  CompleteOrderedField R ->
  R ->
  R ->
  Set
StrictLess reals x y =
  lessOrEqualR reals x y and x != y

doubleNat : Nat -> Nat
doubleNat n =
  n + n

cosineTerm :
  {R : Set} ->
  CompleteOrderedField R ->
  R ->
  Nat ->
  R
cosineTerm reals x zero =
  oneR reals
cosineTerm reals x (suc n) =
  negateR reals
    (multiplyR reals
      (multiplyR reals
        (multiplyR reals (cosineTerm reals x n) x)
        x)
      (inverseR reals
        (multiplyR reals
          (fromNatR reals (suc (doubleNat n)))
          (fromNatR reals (suc (suc (doubleNat n)))))))

cosinePartialSum :
  {R : Set} ->
  CompleteOrderedField R ->
  R ->
  Nat ->
  R
cosinePartialSum reals x zero =
  cosineTerm reals x zero
cosinePartialSum reals x (suc n) =
  addR reals
    (cosinePartialSum reals x n)
    (cosineTerm reals x (suc n))

ConvergesTo :
  {R : Set} ->
  CompleteOrderedField R ->
  (Nat -> R) ->
  R ->
  Set
ConvergesTo reals sequence limit =
  (epsilon : _) ->
  StrictLess reals (zeroR reals) epsilon ->
  Exists Nat
    (\ threshold ->
      (n : Nat) ->
      threshold natLe n ->
      StrictLess reals
        (subtractR reals limit epsilon)
        (sequence n)
      and
      StrictLess reals
        (sequence n)
        (addR reals limit epsilon))

CosineValue :
  {R : Set} ->
  CompleteOrderedField R ->
  R ->
  R ->
  Set
CosineValue reals x value =
  ConvergesTo reals (cosinePartialSum reals x) value

twoR :
  {R : Set} ->
  CompleteOrderedField R ->
  R
twoR reals =
  fromNatR reals (suc (suc zero))

halfOf :
  {R : Set} ->
  CompleteOrderedField R ->
  R ->
  R
halfOf reals x =
  multiplyR reals x (inverseR reals (twoR reals))

PiValue :
  {R : Set} ->
  CompleteOrderedField R ->
  R ->
  Set
PiValue reals piValue =
  StrictLess reals (zeroR reals) piValue
  and
  (CosineValue reals piValue (negateR reals (oneR reals))
  and
  ((x : _) ->
    StrictLess reals (zeroR reals) x ->
    CosineValue reals x (negateR reals (oneR reals)) ->
    lessOrEqualR reals piValue x))

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

open RealInnerProductSpace

NormValue :
  {R V : Set} ->
  (reals : CompleteOrderedField R) ->
  RealInnerProductSpace reals V ->
  V ->
  R ->
  Set
NormValue reals space v length =
  lessOrEqualR reals (zeroR reals) length
  and
  multiplyR reals length length == inner space v v

ZeroVectorAngleValue :
  {R V : Set} ->
  (reals : CompleteOrderedField R) ->
  (space : RealInnerProductSpace reals V) ->
  V ->
  V ->
  R ->
  R ->
  Set
ZeroVectorAngleValue reals space u v piValue angle =
  ((u == zeroV space) or (v == zeroV space))
  and
  angle == halfOf reals piValue

NonzeroVectorAngleValue :
  {R V : Set} ->
  (reals : CompleteOrderedField R) ->
  (space : RealInnerProductSpace reals V) ->
  V ->
  V ->
  R ->
  R ->
  Set
NonzeroVectorAngleValue reals space u v piValue angle =
  ((u != zeroV space) and (v != zeroV space))
  and
  ((lessOrEqualR reals (zeroR reals) angle
    and
    lessOrEqualR reals angle piValue)
  and
  Exists _
    (\ normU ->
      NormValue reals space u normU
      and
      Exists _
        (\ normV ->
          NormValue reals space v normV
          and
          Exists _
            (\ cosineOfAngle ->
              CosineValue reals angle cosineOfAngle
              and
              inner space u v
              ==
              multiplyR reals
                (multiplyR reals normU normV)
                cosineOfAngle))))

VectorAngleValue :
  {R V : Set} ->
  (reals : CompleteOrderedField R) ->
  (space : RealInnerProductSpace reals V) ->
  V ->
  V ->
  R ->
  Set
VectorAngleValue reals space u v angle =
  Exists _
    (\ piValue ->
      PiValue reals piValue
      and
      (ZeroVectorAngleValue reals space u v piValue angle
      or
      NonzeroVectorAngleValue reals space u v piValue angle))

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

AngleAtValue :
  {R V P : Set} ->
  (reals : CompleteOrderedField R) ->
  (space : RealInnerProductSpace reals V) ->
  AffineTorsor space P ->
  P ->
  P ->
  P ->
  R ->
  Set
AngleAtValue reals space affine a vertex c angle =
  VectorAngleValue reals space
    (vsub affine a vertex)
    (vsub affine c vertex)
    angle

StrictBetween :
  {R V P : Set} ->
  (reals : CompleteOrderedField R) ->
  (space : RealInnerProductSpace reals V) ->
  AffineTorsor space P ->
  P ->
  P ->
  P ->
  Set
StrictBetween reals space affine endpoint1 middle endpoint2 =
  endpoint1 != endpoint2
  and
  Exists _
    (\ t ->
      StrictLess reals (zeroR reals) t
      and
      (StrictLess reals t (oneR reals)
      and
      middle ==
        vadd affine
          (scaleV space t (vsub affine endpoint2 endpoint1))
          endpoint1))

exterior-angle-theorem : Set1
exterior-angle-theorem =
  (R V P : Set) ->
  (reals : CompleteOrderedField R) ->
  (space : RealInnerProductSpace reals V) ->
  (affine : AffineTorsor space P) ->
  (p1 p2 p3 p : P) ->
  StrictBetween reals space affine p p1 p2 ->
  Exists _
    (\ exteriorAngle ->
      AngleAtValue reals space affine p3 p1 p exteriorAngle
      and
      Exists _
        (\ remoteAngleAtP3 ->
          AngleAtValue reals space affine p1 p3 p2 remoteAngleAtP3
          and
          Exists _
            (\ remoteAngleAtP2 ->
              AngleAtValue reals space affine p3 p2 p1 remoteAngleAtP2
              and
              exteriorAngle
              ==
              addR reals remoteAngleAtP3 remoteAngleAtP2)))
