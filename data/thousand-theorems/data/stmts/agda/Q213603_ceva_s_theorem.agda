-- Statement-only formalization of thousand-theorems corpus artifact Q213603,
-- "Ceva's theorem": in a normed affine space, three points on the cyclic
-- opposite-side lines of an affine-independent triangle, whose vertex lines
-- meet at one point, have product of the three distance ratios equal to one.
-- This file contains no proof.

{-# OPTIONS --safe #-}

module Q213603_ceva_s_theorem where

open import Agda.Builtin.Equality renaming (_≡_ to _==_)
open import Agda.Builtin.Nat using (Nat; zero; suc)

infix 4 _!=_

data Bottom : Set where

Not : Set -> Set
Not A =
  A -> Bottom

_!=_ : {A : Set} -> A -> A -> Set
x != y =
  Not (x == y)

record Both (A B : Set) : Set where
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

record RealLine (R : Set) : Set1 where
  field
    zeroR oneR : R
    addR multiplyR : R -> R -> R
    negateR reciprocalR absoluteR : R -> R
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
    reciprocal-zeroR :
      reciprocalR zeroR == zeroR
    multiply-reciprocalR :
      (x : R) ->
      x != zeroR ->
      multiplyR x (reciprocalR x) == oneR

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
      Both (lessOrEqualR zeroR oneR) (zeroR != oneR)

    absolute-nonnegativeR :
      (x : R) ->
      lessOrEqualR zeroR (absoluteR x)
    absolute-of-nonnegativeR :
      (x : R) ->
      lessOrEqualR zeroR x ->
      absoluteR x == x
    absolute-of-nonpositiveR :
      (x : R) ->
      lessOrEqualR x zeroR ->
      absoluteR x == negateR x
    absolute-zero-onlyR :
      (x : R) ->
      absoluteR x == zeroR ->
      x == zeroR
    absolute-negateR :
      (x : R) ->
      absoluteR (negateR x) == absoluteR x
    absolute-addR :
      (x y : R) ->
      lessOrEqualR
        (absoluteR (addR x y))
        (addR (absoluteR x) (absoluteR y))
    absolute-multiplyR :
      (x y : R) ->
      absoluteR (multiplyR x y) ==
      multiplyR (absoluteR x) (absoluteR y)

    fromNat-zeroR :
      fromNatR zero == zeroR
    fromNat-successorR :
      (n : Nat) ->
      fromNatR (suc n) == addR (fromNatR n) oneR
    fromNat-injectiveR :
      (m n : Nat) ->
      fromNatR m == fromNatR n ->
      m == n

    archimedeanR :
      (x : R) ->
      Exists Nat
        (\ n ->
          lessOrEqualR x (fromNatR n))
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
          Both
            ((x : R) ->
              P x ->
              lessOrEqualR x supremum)
            ((upper : R) ->
              ((x : R) ->
                P x ->
                lessOrEqualR x upper) ->
              lessOrEqualR supremum upper))

open RealLine

record RealLineEquivalence
  {R S : Set}
  (source : RealLine R)
  (target : RealLine S) :
  Set1 where

  field
    toR : R -> S
    fromR : S -> R
    to-fromR :
      (y : S) ->
      toR (fromR y) == y
    from-toR :
      (x : R) ->
      fromR (toR x) == x
    to-zeroR :
      toR (zeroR source) == zeroR target
    to-oneR :
      toR (oneR source) == oneR target
    to-addR :
      (x y : R) ->
      toR (addR source x y) ==
      addR target (toR x) (toR y)
    to-multiplyR :
      (x y : R) ->
      toR (multiplyR source x y) ==
      multiplyR target (toR x) (toR y)
    to-negateR :
      (x : R) ->
      toR (negateR source x) ==
      negateR target (toR x)
    to-reciprocalR :
      (x : R) ->
      toR (reciprocalR source x) ==
      reciprocalR target (toR x)
    to-absoluteR :
      (x : R) ->
      toR (absoluteR source x) ==
      absoluteR target (toR x)
    to-orderR :
      (x y : R) ->
      Iff
        (lessOrEqualR source x y)
        (lessOrEqualR target (toR x) (toR y))

record RealNumberPresentation
  {R : Set}
  (reals : RealLine R) :
  Set2 where

  field
    equivalent-real-line :
      (S : Set) ->
      (other : RealLine S) ->
      RealLineEquivalence reals other

record NormedField
  (K R : Set)
  (reals : RealLine R) :
  Set1 where

  field
    zeroK oneK : K
    addK multiplyK : K -> K -> K
    negateK reciprocalK : K -> K
    normK : K -> R

    one-not-zeroK :
      oneK != zeroK

    add-commutativeK :
      (x y : K) ->
      addK x y == addK y x
    add-associativeK :
      (x y z : K) ->
      addK (addK x y) z == addK x (addK y z)
    add-zeroK :
      (x : K) ->
      addK x zeroK == x
    add-inverseK :
      (x : K) ->
      addK x (negateK x) == zeroK

    multiply-commutativeK :
      (x y : K) ->
      multiplyK x y == multiplyK y x
    multiply-associativeK :
      (x y z : K) ->
      multiplyK (multiplyK x y) z ==
      multiplyK x (multiplyK y z)
    multiply-oneK :
      (x : K) ->
      multiplyK x oneK == x
    multiply-zeroK :
      (x : K) ->
      multiplyK x zeroK == zeroK
    distributeK :
      (x y z : K) ->
      multiplyK x (addK y z) ==
      addK (multiplyK x y) (multiplyK x z)
    reciprocal-zeroK :
      reciprocalK zeroK == zeroK
    multiply-reciprocalK :
      (x : K) ->
      x != zeroK ->
      multiplyK x (reciprocalK x) == oneK

    norm-nonnegativeK :
      (x : K) ->
      lessOrEqualR reals (zeroR reals) (normK x)
    norm-zeroK :
      normK zeroK == zeroR reals
    norm-zero-onlyK :
      (x : K) ->
      normK x == zeroR reals ->
      x == zeroK
    norm-negateK :
      (x : K) ->
      normK (negateK x) == normK x
    norm-addK :
      (x y : K) ->
      lessOrEqualR reals
        (normK (addK x y))
        (addR reals (normK x) (normK y))
    norm-multiplyK :
      (x y : K) ->
      normK (multiplyK x y) ==
      multiplyR reals (normK x) (normK y)

open NormedField

record SeminormedSpace
  (K R V : Set)
  (reals : RealLine R)
  (scalars : NormedField K R reals) :
  Set1 where

  field
    zeroV : V
    addV : V -> V -> V
    negateV : V -> V
    scaleV : K -> V -> V
    normV : V -> R

    add-commutativeV :
      (x y : V) ->
      addV x y == addV y x
    add-associativeV :
      (x y z : V) ->
      addV (addV x y) z == addV x (addV y z)
    add-zeroV :
      (x : V) ->
      addV x zeroV == x
    add-inverseV :
      (x : V) ->
      addV x (negateV x) == zeroV

    scale-oneV :
      (x : V) ->
      scaleV (oneK scalars) x == x
    scale-associativeV :
      (a b : K) ->
      (x : V) ->
      scaleV (multiplyK scalars a b) x ==
      scaleV a (scaleV b x)
    scale-add-vectorsV :
      (a : K) ->
      (x y : V) ->
      scaleV a (addV x y) ==
      addV (scaleV a x) (scaleV a y)
    scale-add-scalarsV :
      (a b : K) ->
      (x : V) ->
      scaleV (addK scalars a b) x ==
      addV (scaleV a x) (scaleV b x)

    norm-nonnegativeV :
      (x : V) ->
      lessOrEqualR reals (zeroR reals) (normV x)
    norm-zeroV :
      normV zeroV == zeroR reals
    norm-negateV :
      (x : V) ->
      normV (negateV x) == normV x
    norm-addV :
      (x y : V) ->
      lessOrEqualR reals
        (normV (addV x y))
        (addR reals (normV x) (normV y))
    norm-scaleV :
      (a : K) ->
      (x : V) ->
      normV (scaleV a x) ==
      multiplyR reals (normK scalars a) (normV x)

open SeminormedSpace

record NormedAffineSpace
  {K R V : Set}
  {reals : RealLine R}
  {scalars : NormedField K R reals}
  (vectors : SeminormedSpace K R V reals scalars)
  (P : Set) :
  Set1 where

  field
    vadd : V -> P -> P
    vsub : P -> P -> V
    distance : P -> P -> R

    zero-vadd :
      (point : P) ->
      vadd (zeroV vectors) point == point
    add-vadd :
      (u v : V) ->
      (point : P) ->
      vadd (addV vectors u v) point ==
      vadd u (vadd v point)
    vadd-vsub :
      (p q : P) ->
      vadd (vsub p q) q == p
    vsub-vadd :
      (v : V) ->
      (point : P) ->
      vsub (vadd v point) point == v

    distance-nonnegative :
      (p q : P) ->
      lessOrEqualR reals (zeroR reals) (distance p q)
    distance-self :
      (p : P) ->
      distance p p == zeroR reals
    distance-separates :
      (p q : P) ->
      distance p q == zeroR reals ->
      p == q
    distance-symmetric :
      (p q : P) ->
      distance p q == distance q p
    distance-triangle :
      (p q r : P) ->
      lessOrEqualR reals
        (distance p r)
        (addR reals (distance p q) (distance q r))
    distance-vsub :
      (p q : P) ->
      distance p q == normV vectors (vsub p q)

open NormedAffineSpace

data Fin3 : Set where
  index0 index1 index2 : Fin3

next : Fin3 -> Fin3
next index0 = index1
next index1 = index2
next index2 = index0

next2 : Fin3 -> Fin3
next2 i =
  next (next i)

record Triangle
  {K R V P : Set}
  {reals : RealLine R}
  {scalars : NormedField K R reals}
  (vectors : SeminormedSpace K R V reals scalars)
  (affine : NormedAffineSpace vectors P) :
  Set where

  field
    points : Fin3 -> P
    affine-independent :
      (a b : K) ->
      addV vectors
        (scaleV vectors a
          (vsub affine (points index1) (points index0)))
        (scaleV vectors b
          (vsub affine (points index2) (points index0)))
      ==
      zeroV vectors ->
      Both (a == zeroK scalars) (b == zeroK scalars)

open Triangle

OnAffineLine :
  {K R V P : Set} ->
  {reals : RealLine R} ->
  {scalars : NormedField K R reals} ->
  (vectors : SeminormedSpace K R V reals scalars) ->
  (affine : NormedAffineSpace vectors P) ->
  P ->
  P ->
  P ->
  Set
OnAffineLine {K = K} vectors affine a b x =
  Exists K
    (\ r ->
      x ==
      vadd affine
        (scaleV vectors r (vsub affine b a))
        a)

divideR :
  {R : Set} ->
  RealLine R ->
  R ->
  R ->
  R
divideR reals x y =
  multiplyR reals x (reciprocalR reals y)

product3 :
  {R : Set} ->
  RealLine R ->
  (Fin3 -> R) ->
  R
product3 reals f =
  multiplyR reals
    (f index0)
    (multiplyR reals (f index1) (f index2))

cevas-theorem : Set2
cevas-theorem =
  (R : Set) ->
  (reals : RealLine R) ->
  RealNumberPresentation reals ->
  (K V P : Set) ->
  (scalars : NormedField K R reals) ->
  (vectors : SeminormedSpace K R V reals scalars) ->
  (affine : NormedAffineSpace vectors P) ->
  (triangle : Triangle vectors affine) ->
  (sidePoint : Fin3 -> P) ->
  (concurrencePoint : P) ->
  ((i : Fin3) ->
    sidePoint i != points triangle (next2 i)) ->
  ((i : Fin3) ->
    OnAffineLine vectors affine
      (points triangle (next i))
      (points triangle (next2 i))
      (sidePoint i)) ->
  ((i : Fin3) ->
    OnAffineLine vectors affine
      (points triangle i)
      (sidePoint i)
      concurrencePoint) ->
  product3 reals
    (\ i ->
      divideR reals
        (distance affine
          (points triangle (next i))
          (sidePoint i))
        (distance affine
          (sidePoint i)
          (points triangle (next2 i))))
  ==
  oneR reals
