-- Statement-only formalization of thousand-theorems corpus artifact Q866116,
-- "Hahn–Banach theorem": every continuous linear functional on a linear
-- subspace of a seminormed space over the real or complex scalars extends to
-- the whole space without changing its operator norm. This file contains no proof.

{-# OPTIONS --safe #-}

module Q866116_hahn_banach_theorem where

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

-- A complete Archimedean ordered field presents the real scalar line.
record RealLine
  {r : Level}
  (R : Set r) :
  Set (lsuc r) where

  field
    zeroR oneR : R
    addR multiplyR : R -> R -> R
    negateR reciprocalR : R -> R
    lessOrEqualR : R -> R -> Set
    fromNatR : Nat -> R

    one-not-zeroR :
      oneR != zeroR

    add-commutativeR :
      (x y : R) -> addR x y == addR y x
    add-associativeR :
      (x y z : R) ->
      addR (addR x y) z == addR x (addR y z)
    add-zeroR :
      (x : R) -> addR x zeroR == x
    add-inverseR :
      (x : R) -> addR x (negateR x) == zeroR

    multiply-commutativeR :
      (x y : R) -> multiplyR x y == multiplyR y x
    multiply-associativeR :
      (x y z : R) ->
      multiplyR (multiplyR x y) z == multiplyR x (multiplyR y z)
    multiply-oneR :
      (x : R) -> multiplyR x oneR == x
    multiply-zeroR :
      (x : R) -> multiplyR x zeroR == zeroR
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
      (x : R) -> lessOrEqualR x x
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
      (x y : R) -> Either (lessOrEqualR x y) (lessOrEqualR y x)
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

    fromNat-zeroR :
      fromNatR zero == zeroR
    fromNat-successorR :
      (n : Nat) -> fromNatR (suc n) == addR (fromNatR n) oneR
    fromNat-injectiveR :
      (m n : Nat) -> fromNatR m == fromNatR n -> m == n

    archimedeanR :
      (x : R) ->
      Exists Nat (\ n -> lessOrEqualR x (fromNatR n))
    least-upper-boundR :
      (P : R -> Set r) ->
      Exists R P ->
      Exists R (\ upper -> (x : R) -> P x -> lessOrEqualR x upper) ->
      Exists R
        (\ supremum ->
          Both
            ((x : R) -> P x -> lessOrEqualR x supremum)
            ((upper : R) ->
              ((x : R) -> P x -> lessOrEqualR x upper) ->
              lessOrEqualR supremum upper))

open RealLine

data ScalarKind : Set where
  realScalar    : ScalarKind
  complexScalar : ScalarKind

data CanonicalScalar
  {r : Level}
  (R : Set r) :
  ScalarKind ->
  Set r where

  realValue :
    R ->
    CanonicalScalar R realScalar
  complexValue :
    R ->
    R ->
    CanonicalScalar R complexScalar

canonicalZero :
  {r : Level} ->
  {R : Set r} ->
  RealLine R ->
  (kind : ScalarKind) ->
  CanonicalScalar R kind
canonicalZero reals realScalar =
  realValue (zeroR reals)
canonicalZero reals complexScalar =
  complexValue (zeroR reals) (zeroR reals)

canonicalOne :
  {r : Level} ->
  {R : Set r} ->
  RealLine R ->
  (kind : ScalarKind) ->
  CanonicalScalar R kind
canonicalOne reals realScalar =
  realValue (oneR reals)
canonicalOne reals complexScalar =
  complexValue (oneR reals) (zeroR reals)

canonicalAdd :
  {r : Level} ->
  {R : Set r} ->
  RealLine R ->
  (kind : ScalarKind) ->
  CanonicalScalar R kind ->
  CanonicalScalar R kind ->
  CanonicalScalar R kind
canonicalAdd reals realScalar (realValue x) (realValue y) =
  realValue (addR reals x y)
canonicalAdd reals complexScalar (complexValue a b) (complexValue c d) =
  complexValue (addR reals a c) (addR reals b d)

canonicalMultiply :
  {r : Level} ->
  {R : Set r} ->
  RealLine R ->
  (kind : ScalarKind) ->
  CanonicalScalar R kind ->
  CanonicalScalar R kind ->
  CanonicalScalar R kind
canonicalMultiply reals realScalar (realValue x) (realValue y) =
  realValue (multiplyR reals x y)
canonicalMultiply reals complexScalar (complexValue a b) (complexValue c d) =
  complexValue
    (addR reals
      (multiplyR reals a c)
      (negateR reals (multiplyR reals b d)))
    (addR reals
      (multiplyR reals a d)
      (multiplyR reals b c))

canonicalNegate :
  {r : Level} ->
  {R : Set r} ->
  RealLine R ->
  (kind : ScalarKind) ->
  CanonicalScalar R kind ->
  CanonicalScalar R kind
canonicalNegate reals realScalar (realValue x) =
  realValue (negateR reals x)
canonicalNegate reals complexScalar (complexValue a b) =
  complexValue (negateR reals a) (negateR reals b)

CanonicalNormValue :
  {r : Level} ->
  {R : Set r} ->
  (reals : RealLine R) ->
  (kind : ScalarKind) ->
  CanonicalScalar R kind ->
  R ->
  Set r
CanonicalNormValue reals realScalar (realValue x) value =
  Both
    (lessOrEqualR reals (zeroR reals) value)
    (multiplyR reals value value == multiplyR reals x x)
CanonicalNormValue reals complexScalar (complexValue a b) value =
  Both
    (lessOrEqualR reals (zeroR reals) value)
    (multiplyR reals value value ==
      addR reals
        (multiplyR reals a a)
        (multiplyR reals b b))

-- This packages exactly a real or complex scalar field, up to isomorphism.
record RCLike
  {k r : Level}
  (K : Set k)
  (R : Set r)
  (reals : RealLine R) :
  Set (lsuc (k ⊔ r)) where

  field
    scalar-kind :
      ScalarKind
    to-canonical :
      K -> CanonicalScalar R scalar-kind
    from-canonical :
      CanonicalScalar R scalar-kind -> K
    from-after-to-canonical :
      (x : K) ->
      from-canonical (to-canonical x) == x
    to-after-from-canonical :
      (x : CanonicalScalar R scalar-kind) ->
      to-canonical (from-canonical x) == x

    normK :
      K -> R
    norm-canonical :
      (x : K) ->
      CanonicalNormValue reals scalar-kind (to-canonical x) (normK x)

open RCLike

zeroK :
  {k r : Level} ->
  {K : Set k} ->
  {R : Set r} ->
  {reals : RealLine R} ->
  RCLike K R reals ->
  K
zeroK {reals = reals} scalars =
  from-canonical scalars (canonicalZero reals (scalar-kind scalars))

oneK :
  {k r : Level} ->
  {K : Set k} ->
  {R : Set r} ->
  {reals : RealLine R} ->
  RCLike K R reals ->
  K
oneK {reals = reals} scalars =
  from-canonical scalars (canonicalOne reals (scalar-kind scalars))

addK :
  {k r : Level} ->
  {K : Set k} ->
  {R : Set r} ->
  {reals : RealLine R} ->
  (scalars : RCLike K R reals) ->
  K ->
  K ->
  K
addK {reals = reals} scalars x y =
  from-canonical scalars
    (canonicalAdd reals (scalar-kind scalars)
      (to-canonical scalars x)
      (to-canonical scalars y))

multiplyK :
  {k r : Level} ->
  {K : Set k} ->
  {R : Set r} ->
  {reals : RealLine R} ->
  (scalars : RCLike K R reals) ->
  K ->
  K ->
  K
multiplyK {reals = reals} scalars x y =
  from-canonical scalars
    (canonicalMultiply reals (scalar-kind scalars)
      (to-canonical scalars x)
      (to-canonical scalars y))

negateK :
  {k r : Level} ->
  {K : Set k} ->
  {R : Set r} ->
  {reals : RealLine R} ->
  (scalars : RCLike K R reals) ->
  K ->
  K
negateK {reals = reals} scalars x =
  from-canonical scalars
    (canonicalNegate reals (scalar-kind scalars)
      (to-canonical scalars x))

record SeminormedSpace
  {k r v : Level}
  (K : Set k)
  (R : Set r)
  (V : Set v)
  (reals : RealLine R)
  (scalars : RCLike K R reals) :
  Set (lsuc (k ⊔ r ⊔ v)) where

  field
    zeroV : V
    addV : V -> V -> V
    negateV : V -> V
    scaleV : K -> V -> V
    normV : V -> R

    add-commutativeV :
      (x y : V) -> addV x y == addV y x
    add-associativeV :
      (x y z : V) ->
      addV (addV x y) z == addV x (addV y z)
    add-zeroV :
      (x : V) -> addV x zeroV == x
    add-inverseV :
      (x : V) -> addV x (negateV x) == zeroV

    scale-oneV :
      (x : V) -> scaleV (oneK scalars) x == x
    scale-associativeV :
      (a b : K) ->
      (x : V) ->
      scaleV (multiplyK scalars a b) x == scaleV a (scaleV b x)
    scale-add-vectorsV :
      (a : K) ->
      (x y : V) ->
      scaleV a (addV x y) == addV (scaleV a x) (scaleV a y)
    scale-add-scalarsV :
      (a b : K) ->
      (x : V) ->
      scaleV (addK scalars a b) x == addV (scaleV a x) (scaleV b x)

    norm-nonnegativeV :
      (x : V) -> lessOrEqualR reals (zeroR reals) (normV x)
    norm-zeroV :
      normV zeroV == zeroR reals
    norm-negateV :
      (x : V) -> normV (negateV x) == normV x
    norm-addV :
      (x y : V) ->
      lessOrEqualR reals (normV (addV x y))
        (addR reals (normV x) (normV y))
    norm-scaleV :
      (a : K) ->
      (x : V) ->
      normV (scaleV a x) ==
      multiplyR reals (normK scalars a) (normV x)

open SeminormedSpace

-- A bundled carrier with an isometric injective linear inclusion.
record LinearSubspace
  {k r e : Level}
  {K : Set k}
  {R : Set r}
  {E : Set e}
  {reals : RealLine R}
  {scalars : RCLike K R reals}
  (ambient : SeminormedSpace K R E reals scalars) :
  Set (lsuc (k ⊔ r ⊔ e)) where

  field
    Carrier :
      Set e
    subspaceSpace :
      SeminormedSpace K R Carrier reals scalars
    include :
      Carrier -> E
    include-injective :
      (x y : Carrier) ->
      include x == include y ->
      x == y
    include-zero :
      include (zeroV subspaceSpace) == zeroV ambient
    include-add :
      (x y : Carrier) ->
      include (addV subspaceSpace x y) ==
      addV ambient (include x) (include y)
    include-scale :
      (a : K) ->
      (x : Carrier) ->
      include (scaleV subspaceSpace a x) ==
      scaleV ambient a (include x)
    include-norm :
      (x : Carrier) ->
      normV subspaceSpace x == normV ambient (include x)

open LinearSubspace

-- Bounded linear functionals carry the least nonnegative bound, their
-- operator norm, as data characterized by its universal property.
record ContinuousLinearFunctional
  {k r v : Level}
  {K : Set k}
  {R : Set r}
  {V : Set v}
  {reals : RealLine R}
  {scalars : RCLike K R reals}
  (domain : SeminormedSpace K R V reals scalars) :
  Set (lsuc (k ⊔ r ⊔ v)) where

  field
    apply :
      V -> K
    map-add :
      (x y : V) ->
      apply (addV domain x y) ==
      addK scalars (apply x) (apply y)
    map-scale :
      (a : K) ->
      (x : V) ->
      apply (scaleV domain a x) ==
      multiplyK scalars a (apply x)

    operatorNorm :
      R
    operatorNorm-nonnegative :
      lessOrEqualR reals (zeroR reals) operatorNorm
    operatorNorm-bounds :
      (x : V) ->
      lessOrEqualR reals
        (normK scalars (apply x))
        (multiplyR reals operatorNorm (normV domain x))
    operatorNorm-least :
      (bound : R) ->
      lessOrEqualR reals (zeroR reals) bound ->
      ((x : V) ->
        lessOrEqualR reals
          (normK scalars (apply x))
          (multiplyR reals bound (normV domain x))) ->
      lessOrEqualR reals operatorNorm bound

open ContinuousLinearFunctional

hahn-banach-theorem :
  {r k e : Level} ->
  Set (lsuc (r ⊔ k ⊔ e))
hahn-banach-theorem {r} {k} {e} =
  (R : Set r) ->
  (K : Set k) ->
  (E : Set e) ->
  (reals : RealLine R) ->
  (scalars : RCLike K R reals) ->
  (ambient : SeminormedSpace K R E reals scalars) ->
  (subspace : LinearSubspace ambient) ->
  (f : ContinuousLinearFunctional (subspaceSpace subspace)) ->
  Exists (ContinuousLinearFunctional ambient)
    (\ g ->
      Both
        ((x : Carrier subspace) ->
          apply g (include subspace x) == apply f x)
        (operatorNorm g == operatorNorm f))
