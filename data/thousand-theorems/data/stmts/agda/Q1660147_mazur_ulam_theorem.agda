-- Statement-only formalization of thousand-theorems corpus artifact Q1660147
-- (thousand-theorems__agda__Q1660147), "Mazur–Ulam theorem": every bijective
-- isometry between real normed affine spaces is an affine isometry with the
-- same underlying forward and inverse maps. This file contains no proof.

{-# OPTIONS --safe #-}

module Q1660147_mazur_ulam_theorem where

open import Agda.Primitive using (Level; lsuc; _⊔_)
open import Agda.Builtin.Equality renaming (_≡_ to _==_)
open import Agda.Builtin.Nat using (Nat; zero; suc)

infix 4 _!=_

data Bottom {a : Level} : Set a where

Not :
  {a : Level} ->
  Set a ->
  Set a
Not {a} A =
  A -> Bottom {a}

_!=_ :
  {a : Level} ->
  {A : Set a} ->
  A ->
  A ->
  Set a
x != y =
  Not (x == y)

record Both
  {a b : Level}
  (A : Set a)
  (B : Set b) :
  Set (a ⊔ b) where

  constructor both
  field
    first  : A
    second : B

data Either
  {a b : Level}
  (A : Set a)
  (B : Set b) :
  Set (a ⊔ b) where

  left  : A -> Either A B
  right : B -> Either A B

record Exists
  {a p : Level}
  (A : Set a)
  (P : A -> Set p) :
  Set (a ⊔ p) where

  constructor witness
  field
    value    : A
    property : P value

record RealLine
  {r : Level}
  (R : Set r) :
  Set (lsuc r) where

  field
    zeroR oneR : R
    addR multiplyR : R -> R -> R
    negateR reciprocalR absoluteR : R -> R
    lessOrEqualR : R -> R -> Set r
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
      (P : R -> Set r) ->
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

record RealNormedVectorSpace
  {r e : Level}
  {R : Set r}
  (reals : RealLine R)
  (E : Set e) :
  Set (lsuc (r ⊔ e)) where

  field
    zeroV : E
    addV : E -> E -> E
    negateV : E -> E
    scaleV : R -> E -> E
    normV : E -> R

    add-commutativeV :
      (x y : E) ->
      addV x y == addV y x
    add-associativeV :
      (x y z : E) ->
      addV (addV x y) z == addV x (addV y z)
    add-zeroV :
      (x : E) ->
      addV x zeroV == x
    add-inverseV :
      (x : E) ->
      addV x (negateV x) == zeroV

    scale-oneV :
      (x : E) ->
      scaleV (oneR reals) x == x
    scale-associativeV :
      (a b : R) ->
      (x : E) ->
      scaleV (multiplyR reals a b) x ==
      scaleV a (scaleV b x)
    scale-add-vectorsV :
      (a : R) ->
      (x y : E) ->
      scaleV a (addV x y) ==
      addV (scaleV a x) (scaleV a y)
    scale-add-scalarsV :
      (a b : R) ->
      (x : E) ->
      scaleV (addR reals a b) x ==
      addV (scaleV a x) (scaleV b x)

    norm-nonnegativeV :
      (x : E) ->
      lessOrEqualR reals (zeroR reals) (normV x)
    norm-zeroV :
      normV zeroV == zeroR reals
    norm-zero-onlyV :
      (x : E) ->
      normV x == zeroR reals ->
      x == zeroV
    norm-addV :
      (x y : E) ->
      lessOrEqualR reals
        (normV (addV x y))
        (addR reals (normV x) (normV y))
    norm-scaleV :
      (a : R) ->
      (x : E) ->
      normV (scaleV a x) ==
      multiplyR reals (absoluteR reals a) (normV x)

open RealNormedVectorSpace

record NormedAddTorsor
  {r e p : Level}
  {R : Set r}
  {E : Set e}
  {reals : RealLine R}
  (vectors : RealNormedVectorSpace reals E)
  (P : Set p) :
  Set (lsuc (r ⊔ e ⊔ p)) where

  field
    basePoint : P
    vadd : E -> P -> P
    vsub : P -> P -> E

    zero-vadd :
      (point : P) ->
      vadd (zeroV vectors) point == point
    add-vadd :
      (u v : E) ->
      (point : P) ->
      vadd (addV vectors u v) point ==
      vadd u (vadd v point)
    vadd-vsub :
      (p1 p2 : P) ->
      vadd (vsub p1 p2) p2 == p1
    vsub-vadd :
      (v : E) ->
      (point : P) ->
      vsub (vadd v point) point == v

open NormedAddTorsor

distance :
  {r e p : Level} ->
  {R : Set r} ->
  {E : Set e} ->
  {P : Set p} ->
  {reals : RealLine R} ->
  {vectors : RealNormedVectorSpace reals E} ->
  NormedAddTorsor vectors P ->
  P ->
  P ->
  R
distance {vectors = vectors} affine p q =
  normV vectors (vsub affine p q)

record IsometryEquiv
  {r e pe f pf : Level}
  {R : Set r}
  {E : Set e}
  {PE : Set pe}
  {F : Set f}
  {PF : Set pf}
  {reals : RealLine R}
  {sourceVectors : RealNormedVectorSpace reals E}
  {targetVectors : RealNormedVectorSpace reals F}
  (sourceAffine : NormedAddTorsor sourceVectors PE)
  (targetAffine : NormedAddTorsor targetVectors PF) :
  Set (r ⊔ e ⊔ pe ⊔ f ⊔ pf) where

  field
    forward : PE -> PF
    backward : PF -> PE
    forward-after-backward :
      (y : PF) ->
      forward (backward y) == y
    backward-after-forward :
      (x : PE) ->
      backward (forward x) == x
    forward-distance :
      (x y : PE) ->
      distance targetAffine (forward x) (forward y) ==
      distance sourceAffine x y

open IsometryEquiv

record LinearIsometryEquiv
  {r e f : Level}
  {R : Set r}
  {E : Set e}
  {F : Set f}
  {reals : RealLine R}
  (source : RealNormedVectorSpace reals E)
  (target : RealNormedVectorSpace reals F) :
  Set (r ⊔ e ⊔ f) where

  field
    forwardLinear : E -> F
    backwardLinear : F -> E
    forward-after-backwardLinear :
      (y : F) ->
      forwardLinear (backwardLinear y) == y
    backward-after-forwardLinear :
      (x : E) ->
      backwardLinear (forwardLinear x) == x
    forward-addLinear :
      (x y : E) ->
      forwardLinear (addV source x y) ==
      addV target (forwardLinear x) (forwardLinear y)
    forward-scaleLinear :
      (a : R) ->
      (x : E) ->
      forwardLinear (scaleV source a x) ==
      scaleV target a (forwardLinear x)
    forward-normLinear :
      (x : E) ->
      normV target (forwardLinear x) ==
      normV source x

open LinearIsometryEquiv

record AffineIsometryEquiv
  {r e pe f pf : Level}
  {R : Set r}
  {E : Set e}
  {PE : Set pe}
  {F : Set f}
  {PF : Set pf}
  {reals : RealLine R}
  (sourceVectors : RealNormedVectorSpace reals E)
  (targetVectors : RealNormedVectorSpace reals F)
  (sourceAffine : NormedAddTorsor sourceVectors PE)
  (targetAffine : NormedAddTorsor targetVectors PF) :
  Set (r ⊔ e ⊔ pe ⊔ f ⊔ pf) where

  field
    toIsometryEquiv :
      IsometryEquiv sourceAffine targetAffine
    linearPart :
      LinearIsometryEquiv sourceVectors targetVectors
    map-vadd :
      (v : E) ->
      (point : PE) ->
      forward toIsometryEquiv (vadd sourceAffine v point) ==
      vadd targetAffine
        (forwardLinear linearPart v)
        (forward toIsometryEquiv point)

open AffineIsometryEquiv

mazur-ulam-theorem :
  (r e pe f pf : Level) ->
  Set (lsuc (r ⊔ e ⊔ pe ⊔ f ⊔ pf))
mazur-ulam-theorem r e pe f pf =
  (R : Set r) ->
  (reals : RealLine R) ->
  (E : Set e) ->
  (sourceVectors : RealNormedVectorSpace reals E) ->
  (PE : Set pe) ->
  (sourceAffine : NormedAddTorsor sourceVectors PE) ->
  (F : Set f) ->
  (targetVectors : RealNormedVectorSpace reals F) ->
  (PF : Set pf) ->
  (targetAffine : NormedAddTorsor targetVectors PF) ->
  (isometry : IsometryEquiv sourceAffine targetAffine) ->
  Exists
    (AffineIsometryEquiv
      sourceVectors targetVectors sourceAffine targetAffine)
    (\ affineIsometry ->
      Both
        ((x : PE) ->
          forward (toIsometryEquiv affineIsometry) x ==
          forward isometry x)
        ((y : PF) ->
          backward (toIsometryEquiv affineIsometry) y ==
          backward isometry y))
