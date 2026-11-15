-- Statement-only formalization of thousand-theorems corpus artifact Q1472120,
-- "Hellinger&ndash;Toeplitz theorem": every everywhere-defined symmetric linear
-- operator on a complete real or complex inner-product space is continuous.
-- This file contains no proof.

{-# OPTIONS --safe #-}

module Q1472120_hellinger_ndash_toeplitz_theorem where

open import Agda.Builtin.Equality renaming (_≡_ to _==_)
open import Agda.Builtin.Nat using (Nat; zero; suc)

infix 4 _!=_ _<=N_

data Bottom : Set where

Not : Set -> Set
Not A = A -> Bottom

_!=_ : {A : Set} -> A -> A -> Set
x != y = Not (x == y)

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

data _<=N_ : Nat -> Nat -> Set where
  zero<=   : {n : Nat} -> zero <=N n
  suc<=suc : {m n : Nat} -> m <=N n -> suc m <=N suc n

record CompleteOrderedField (R : Set) : Set1 where
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
      (P : R -> Set) ->
      Exists R P ->
      Exists R (\ upper -> (x : R) -> P x -> lessOrEqualR x upper) ->
      Exists R
        (\ supremum ->
          Both
            ((x : R) -> P x -> lessOrEqualR x supremum)
            ((upper : R) ->
              ((x : R) -> P x -> lessOrEqualR x upper) ->
              lessOrEqualR supremum upper))

open CompleteOrderedField

StrictLess :
  {R : Set} ->
  CompleteOrderedField R ->
  R ->
  R ->
  Set
StrictLess reals x y =
  Both (lessOrEqualR reals x y) (x != y)

Positive :
  {R : Set} ->
  CompleteOrderedField R ->
  R ->
  Set
Positive reals x =
  StrictLess reals (zeroR reals) x

data ScalarKind : Set where
  realScalar    : ScalarKind
  complexScalar : ScalarKind

data CanonicalScalar (R : Set) : ScalarKind -> Set where
  realValue :
    R ->
    CanonicalScalar R realScalar
  complexValue :
    R ->
    R ->
    CanonicalScalar R complexScalar

canonicalZero :
  {R : Set} ->
  CompleteOrderedField R ->
  (kind : ScalarKind) ->
  CanonicalScalar R kind
canonicalZero reals realScalar =
  realValue (zeroR reals)
canonicalZero reals complexScalar =
  complexValue (zeroR reals) (zeroR reals)

canonicalOne :
  {R : Set} ->
  CompleteOrderedField R ->
  (kind : ScalarKind) ->
  CanonicalScalar R kind
canonicalOne reals realScalar =
  realValue (oneR reals)
canonicalOne reals complexScalar =
  complexValue (oneR reals) (zeroR reals)

canonicalAdd :
  {R : Set} ->
  CompleteOrderedField R ->
  (kind : ScalarKind) ->
  CanonicalScalar R kind ->
  CanonicalScalar R kind ->
  CanonicalScalar R kind
canonicalAdd reals realScalar (realValue x) (realValue y) =
  realValue (addR reals x y)
canonicalAdd reals complexScalar (complexValue a b) (complexValue c d) =
  complexValue
    (addR reals a c)
    (addR reals b d)

canonicalMultiply :
  {R : Set} ->
  CompleteOrderedField R ->
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
  {R : Set} ->
  CompleteOrderedField R ->
  (kind : ScalarKind) ->
  CanonicalScalar R kind ->
  CanonicalScalar R kind
canonicalNegate reals realScalar (realValue x) =
  realValue (negateR reals x)
canonicalNegate reals complexScalar (complexValue a b) =
  complexValue (negateR reals a) (negateR reals b)

canonicalConjugate :
  {R : Set} ->
  CompleteOrderedField R ->
  (kind : ScalarKind) ->
  CanonicalScalar R kind ->
  CanonicalScalar R kind
canonicalConjugate reals realScalar (realValue x) =
  realValue x
canonicalConjugate reals complexScalar (complexValue a b) =
  complexValue a (negateR reals b)

canonicalRealPart :
  {R : Set} ->
  (kind : ScalarKind) ->
  CanonicalScalar R kind ->
  R
canonicalRealPart realScalar (realValue x) =
  x
canonicalRealPart complexScalar (complexValue a b) =
  a

CanonicalReciprocal :
  {R : Set} ->
  (reals : CompleteOrderedField R) ->
  (kind : ScalarKind) ->
  CanonicalScalar R kind ->
  CanonicalScalar R kind ->
  Set
CanonicalReciprocal reals kind x y =
  Both
    (x == canonicalZero reals kind -> y == canonicalZero reals kind)
    (x != canonicalZero reals kind ->
      canonicalMultiply reals kind x y == canonicalOne reals kind)

CanonicalNormValue :
  {R : Set} ->
  (reals : CompleteOrderedField R) ->
  (kind : ScalarKind) ->
  CanonicalScalar R kind ->
  R ->
  Set
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

record RCLike
  (K R : Set)
  (reals : CompleteOrderedField R) : Set1 where
  field
    zeroK oneK : K
    addK multiplyK : K -> K -> K
    negateK reciprocalK conjugateK : K -> K
    realPartK : K -> R
    normK : K -> R

    one-not-zeroK :
      oneK != zeroK

    add-commutativeK :
      (x y : K) -> addK x y == addK y x
    add-associativeK :
      (x y z : K) ->
      addK (addK x y) z == addK x (addK y z)
    add-zeroK :
      (x : K) -> addK x zeroK == x
    add-inverseK :
      (x : K) -> addK x (negateK x) == zeroK

    multiply-commutativeK :
      (x y : K) -> multiplyK x y == multiplyK y x
    multiply-associativeK :
      (x y z : K) ->
      multiplyK (multiplyK x y) z == multiplyK x (multiplyK y z)
    multiply-oneK :
      (x : K) -> multiplyK x oneK == x
    multiply-zeroK :
      (x : K) -> multiplyK x zeroK == zeroK
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

    conjugate-involutiveK :
      (x : K) -> conjugateK (conjugateK x) == x
    conjugate-addK :
      (x y : K) ->
      conjugateK (addK x y) == addK (conjugateK x) (conjugateK y)
    conjugate-multiplyK :
      (x y : K) ->
      conjugateK (multiplyK x y) ==
      multiplyK (conjugateK x) (conjugateK y)
    conjugate-zeroK :
      conjugateK zeroK == zeroK
    conjugate-oneK :
      conjugateK oneK == oneK

    real-part-zeroK :
      realPartK zeroK == zeroR reals
    real-part-oneK :
      realPartK oneK == oneR reals
    real-part-addK :
      (x y : K) ->
      realPartK (addK x y) ==
      addR reals (realPartK x) (realPartK y)
    real-part-conjugateK :
      (x : K) -> realPartK (conjugateK x) == realPartK x

    norm-nonnegativeK :
      (x : K) ->
      lessOrEqualR reals (zeroR reals) (normK x)
    norm-zeroK :
      normK zeroK == zeroR reals
    norm-zero-onlyK :
      (x : K) -> normK x == zeroR reals -> x == zeroK
    norm-negateK :
      (x : K) -> normK (negateK x) == normK x
    norm-conjugateK :
      (x : K) -> normK (conjugateK x) == normK x
    norm-addK :
      (x y : K) ->
      lessOrEqualR reals
        (normK (addK x y))
        (addR reals (normK x) (normK y))
    norm-multiplyK :
      (x y : K) ->
      normK (multiplyK x y) ==
      multiplyR reals (normK x) (normK y)
    norm-squareK :
      (x : K) ->
      multiplyR reals (normK x) (normK x) ==
      realPartK (multiplyK (conjugateK x) x)

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

    to-canonical-zero :
      to-canonical zeroK == canonicalZero reals scalar-kind
    to-canonical-one :
      to-canonical oneK == canonicalOne reals scalar-kind
    to-canonical-add :
      (x y : K) ->
      to-canonical (addK x y) ==
      canonicalAdd reals scalar-kind (to-canonical x) (to-canonical y)
    to-canonical-multiply :
      (x y : K) ->
      to-canonical (multiplyK x y) ==
      canonicalMultiply reals scalar-kind (to-canonical x) (to-canonical y)
    to-canonical-negate :
      (x : K) ->
      to-canonical (negateK x) ==
      canonicalNegate reals scalar-kind (to-canonical x)
    to-canonical-reciprocal :
      (x : K) ->
      CanonicalReciprocal reals scalar-kind
        (to-canonical x)
        (to-canonical (reciprocalK x))
    to-canonical-conjugate :
      (x : K) ->
      to-canonical (conjugateK x) ==
      canonicalConjugate reals scalar-kind (to-canonical x)
    to-canonical-real-part :
      (x : K) ->
      realPartK x == canonicalRealPart scalar-kind (to-canonical x)
    to-canonical-norm :
      (x : K) ->
      CanonicalNormValue reals scalar-kind (to-canonical x) (normK x)

    completeK :
      (sequence : Nat -> K) ->
      ((epsilon : R) ->
        Positive reals epsilon ->
        Exists Nat
          (\ cutoff ->
            (m n : Nat) ->
            cutoff <=N m ->
            cutoff <=N n ->
            StrictLess reals
              (normK
                (addK (sequence m) (negateK (sequence n))))
              epsilon)) ->
      Exists K
        (\ limit ->
          (epsilon : R) ->
          Positive reals epsilon ->
          Exists Nat
            (\ cutoff ->
              (n : Nat) ->
              cutoff <=N n ->
              StrictLess reals
                (normK
                  (addK (sequence n) (negateK limit)))
                epsilon))

open RCLike

record InnerProductSpace
  (K R E : Set)
  (reals : CompleteOrderedField R)
  (scalars : RCLike K R reals) : Set1 where
  field
    zeroE : E
    addE : E -> E -> E
    negateE : E -> E
    scaleE : K -> E -> E
    normE : E -> R
    inner : E -> E -> K

    add-commutativeE :
      (x y : E) -> addE x y == addE y x
    add-associativeE :
      (x y z : E) ->
      addE (addE x y) z == addE x (addE y z)
    add-zeroE :
      (x : E) -> addE x zeroE == x
    add-inverseE :
      (x : E) -> addE x (negateE x) == zeroE

    scale-oneE :
      (x : E) -> scaleE (oneK scalars) x == x
    scale-associativeE :
      (a b : K) ->
      (x : E) ->
      scaleE (multiplyK scalars a b) x == scaleE a (scaleE b x)
    scale-add-vectorsE :
      (a : K) ->
      (x y : E) ->
      scaleE a (addE x y) == addE (scaleE a x) (scaleE a y)
    scale-add-scalarsE :
      (a b : K) ->
      (x : E) ->
      scaleE (addK scalars a b) x == addE (scaleE a x) (scaleE b x)

    norm-nonnegativeE :
      (x : E) ->
      lessOrEqualR reals (zeroR reals) (normE x)
    norm-zeroE :
      normE zeroE == zeroR reals
    norm-zero-onlyE :
      (x : E) -> normE x == zeroR reals -> x == zeroE
    norm-negateE :
      (x : E) -> normE (negateE x) == normE x
    norm-addE :
      (x y : E) ->
      lessOrEqualR reals
        (normE (addE x y))
        (addR reals (normE x) (normE y))
    norm-scaleE :
      (a : K) ->
      (x : E) ->
      normE (scaleE a x) ==
      multiplyR reals (normK scalars a) (normE x)

    inner-add-left :
      (x y z : E) ->
      inner (addE x y) z ==
      addK scalars (inner x z) (inner y z)
    inner-scale-left :
      (a : K) ->
      (x y : E) ->
      inner (scaleE a x) y ==
      multiplyK scalars (conjugateK scalars a) (inner x y)
    inner-add-right :
      (x y z : E) ->
      inner x (addE y z) ==
      addK scalars (inner x y) (inner x z)
    inner-scale-right :
      (a : K) ->
      (x y : E) ->
      inner x (scaleE a y) ==
      multiplyK scalars a (inner x y)
    inner-conjugate-symmetry :
      (x y : E) ->
      inner x y == conjugateK scalars (inner y x)
    inner-nonnegative :
      (x : E) ->
      lessOrEqualR reals
        (zeroR reals)
        (realPartK scalars (inner x x))
    inner-definite :
      (x : E) ->
      inner x x == zeroK scalars ->
      x == zeroE
    inner-norm-square :
      (x : E) ->
      multiplyR reals (normE x) (normE x) ==
      realPartK scalars (inner x x)

open InnerProductSpace

distanceE :
  {K R E : Set} ->
  {reals : CompleteOrderedField R} ->
  {scalars : RCLike K R reals} ->
  InnerProductSpace K R E reals scalars ->
  E ->
  E ->
  R
distanceE space x y =
  normE space (addE space x (negateE space y))

SequentialLimit :
  {K R E : Set} ->
  {reals : CompleteOrderedField R} ->
  {scalars : RCLike K R reals} ->
  InnerProductSpace K R E reals scalars ->
  (Nat -> E) ->
  E ->
  Set
SequentialLimit {R = R} {reals = reals} space sequence limit =
  (epsilon : R) ->
  Positive reals epsilon ->
  Exists Nat
    (\ cutoff ->
      (n : Nat) ->
      cutoff <=N n ->
      StrictLess reals (distanceE space (sequence n) limit) epsilon)

CauchySequence :
  {K R E : Set} ->
  {reals : CompleteOrderedField R} ->
  {scalars : RCLike K R reals} ->
  InnerProductSpace K R E reals scalars ->
  (Nat -> E) ->
  Set
CauchySequence {R = R} {reals = reals} space sequence =
  (epsilon : R) ->
  Positive reals epsilon ->
  Exists Nat
    (\ cutoff ->
      (m n : Nat) ->
      cutoff <=N m ->
      cutoff <=N n ->
      StrictLess reals
        (distanceE space (sequence m) (sequence n))
        epsilon)

Complete :
  {K R E : Set} ->
  {reals : CompleteOrderedField R} ->
  {scalars : RCLike K R reals} ->
  InnerProductSpace K R E reals scalars ->
  Set
Complete {E = E} space =
  (sequence : Nat -> E) ->
  CauchySequence space sequence ->
  Exists E (\ limit -> SequentialLimit space sequence limit)

record LinearEndomorphism
  {K R E : Set}
  {reals : CompleteOrderedField R}
  {scalars : RCLike K R reals}
  (space : InnerProductSpace K R E reals scalars) : Set1 where
  field
    apply : E -> E
    map-add :
      (x y : E) ->
      apply (addE space x y) ==
      addE space (apply x) (apply y)
    map-scale :
      (a : K) ->
      (x : E) ->
      apply (scaleE space a x) ==
      scaleE space a (apply x)

open LinearEndomorphism

Symmetric :
  {K R E : Set} ->
  {reals : CompleteOrderedField R} ->
  {scalars : RCLike K R reals} ->
  {space : InnerProductSpace K R E reals scalars} ->
  LinearEndomorphism space ->
  Set
Symmetric {E = E} {space = space} linear =
  (x y : E) ->
  inner space (apply linear x) y ==
  inner space x (apply linear y)

Continuous :
  {K R E : Set} ->
  {reals : CompleteOrderedField R} ->
  {scalars : RCLike K R reals} ->
  (space : InnerProductSpace K R E reals scalars) ->
  LinearEndomorphism space ->
  Set
Continuous {R = R} {E = E} {reals = reals} space linear =
  (x : E) ->
  (epsilon : R) ->
  Positive reals epsilon ->
  Exists R
    (\ delta ->
      Both
        (Positive reals delta)
        ((y : E) ->
          StrictLess reals (distanceE space y x) delta ->
          StrictLess reals
            (distanceE space (apply linear y) (apply linear x))
            epsilon))

hellinger-toeplitz-theorem : Set1
hellinger-toeplitz-theorem =
  (R K E : Set) ->
  (reals : CompleteOrderedField R) ->
  (scalars : RCLike K R reals) ->
  (space : InnerProductSpace K R E reals scalars) ->
  Complete space ->
  (linear : LinearEndomorphism space) ->
  Symmetric linear ->
  Continuous space linear
