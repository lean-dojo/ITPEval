-- Statement-only formalization of thousand-theorems corpus artifact Q944297,
-- "Open mapping theorem (functional analysis)": a surjective continuous semilinear map
-- between complete normed spaces over isometrically isomorphic nontrivially normed
-- fields maps every open set to an open set. This file contains no proof.

{-# OPTIONS --safe #-}

module Q944297OpenMappingTheoremFunctionalAnalysis where

open import Agda.Builtin.Equality renaming (_≡_ to _==_)
open import Agda.Builtin.Nat using (Nat; zero; suc)

infix 4 _!=_ _<=N_

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

data _<=N_ : Nat -> Nat -> Set where
  zero<=   : {n : Nat} -> zero <=N n
  suc<=suc : {m n : Nat} -> m <=N n -> suc m <=N suc n

record CompleteOrderedField (R : Set) : Set1 where
  field
    zeroR oneR : R
    addR multiplyR : R -> R -> R
    negateR reciprocalR absoluteR : R -> R
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

    absolute-nonnegativeR :
      (x : R) -> lessOrEqualR zeroR (absoluteR x)
    absolute-of-nonnegativeR :
      (x : R) ->
      lessOrEqualR zeroR x ->
      absoluteR x == x
    absolute-of-nonpositiveR :
      (x : R) ->
      lessOrEqualR x zeroR ->
      absoluteR x == negateR x
    absolute-zero-onlyR :
      (x : R) -> absoluteR x == zeroR -> x == zeroR
    absolute-negateR :
      (x : R) -> absoluteR (negateR x) == absoluteR x
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

record NontriviallyNormedField
  (K R : Set)
  (reals : CompleteOrderedField R) : Set1 where
  field
    zeroK oneK : K
    addK multiplyK : K -> K -> K
    negateK reciprocalK : K -> K
    normK : K -> R

    one-not-zeroK :
      oneK != zeroK
    norm-greater-than-oneK :
      Exists K
        (\ x ->
          StrictLess reals (oneR reals) (normK x))

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

    norm-nonnegativeK :
      (x : K) -> lessOrEqualR reals (zeroR reals) (normK x)
    norm-zeroK :
      normK zeroK == zeroR reals
    norm-zero-onlyK :
      (x : K) -> normK x == zeroR reals -> x == zeroK
    norm-negateK :
      (x : K) -> normK (negateK x) == normK x
    norm-addK :
      (x y : K) ->
      lessOrEqualR reals
        (normK (addK x y))
        (addR reals (normK x) (normK y))
    norm-multiplyK :
      (x y : K) ->
      normK (multiplyK x y) ==
      multiplyR reals (normK x) (normK y)

open NontriviallyNormedField

record IsometricRingHom
  {K K2 R : Set}
  {reals : CompleteOrderedField R}
  (source : NontriviallyNormedField K R reals)
  (target : NontriviallyNormedField K2 R reals) : Set where
  field
    mapScalar : K -> K2
    map-zero :
      mapScalar (zeroK source) == zeroK target
    map-one :
      mapScalar (oneK source) == oneK target
    map-add :
      (a b : K) ->
      mapScalar (addK source a b) ==
      addK target (mapScalar a) (mapScalar b)
    map-multiply :
      (a b : K) ->
      mapScalar (multiplyK source a b) ==
      multiplyK target (mapScalar a) (mapScalar b)
    map-isometry :
      (a : K) ->
      normK target (mapScalar a) == normK source a

open IsometricRingHom

record InverseRingHomPair
  {K K2 R : Set}
  {reals : CompleteOrderedField R}
  {source : NontriviallyNormedField K R reals}
  {target : NontriviallyNormedField K2 R reals}
  (forward : IsometricRingHom source target)
  (backward : IsometricRingHom target source) : Set where
  field
    backward-after-forward :
      (a : K) ->
      mapScalar backward (mapScalar forward a) == a
    forward-after-backward :
      (b : K2) ->
      mapScalar forward (mapScalar backward b) == b

record NormedSpace
  (K R V : Set)
  (reals : CompleteOrderedField R)
  (scalars : NontriviallyNormedField K R reals) : Set1 where
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
      scaleV (addK scalars a b) x ==
      addV (scaleV a x) (scaleV b x)

    norm-nonnegativeV :
      (x : V) -> lessOrEqualR reals (zeroR reals) (normV x)
    norm-zeroV :
      normV zeroV == zeroR reals
    norm-zero-onlyV :
      (x : V) -> normV x == zeroR reals -> x == zeroV
    norm-negateV :
      (x : V) -> normV (negateV x) == normV x
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

open NormedSpace

subtractV :
  {K R V : Set} ->
  {reals : CompleteOrderedField R} ->
  {scalars : NontriviallyNormedField K R reals} ->
  NormedSpace K R V reals scalars ->
  V ->
  V ->
  V
subtractV space x y =
  addV space x (negateV space y)

distanceV :
  {K R V : Set} ->
  {reals : CompleteOrderedField R} ->
  {scalars : NontriviallyNormedField K R reals} ->
  NormedSpace K R V reals scalars ->
  V ->
  V ->
  R
distanceV space x y =
  normV space (subtractV space x y)

SequentialLimit :
  {K R V : Set} ->
  {reals : CompleteOrderedField R} ->
  {scalars : NontriviallyNormedField K R reals} ->
  NormedSpace K R V reals scalars ->
  (Nat -> V) ->
  V ->
  Set
SequentialLimit {R = R} {reals = reals} space sequence limit =
  (epsilon : R) ->
  Positive reals epsilon ->
  Exists Nat
    (\ cutoff ->
      (n : Nat) ->
      cutoff <=N n ->
      StrictLess reals (distanceV space (sequence n) limit) epsilon)

CauchySequence :
  {K R V : Set} ->
  {reals : CompleteOrderedField R} ->
  {scalars : NontriviallyNormedField K R reals} ->
  NormedSpace K R V reals scalars ->
  (Nat -> V) ->
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
        (distanceV space (sequence m) (sequence n))
        epsilon)

Complete :
  {K R V : Set} ->
  {reals : CompleteOrderedField R} ->
  {scalars : NontriviallyNormedField K R reals} ->
  NormedSpace K R V reals scalars ->
  Set
Complete {V = V} space =
  (sequence : Nat -> V) ->
  CauchySequence space sequence ->
  Exists V (\ limit -> SequentialLimit space sequence limit)

record ContinuousSemilinearMap
  {K K2 R E F : Set}
  {reals : CompleteOrderedField R}
  {sourceScalars : NontriviallyNormedField K R reals}
  {targetScalars : NontriviallyNormedField K2 R reals}
  (scalarHom : IsometricRingHom sourceScalars targetScalars)
  (domain : NormedSpace K R E reals sourceScalars)
  (codomain : NormedSpace K2 R F reals targetScalars) : Set where
  field
    apply : E -> F
    map-add-vector :
      (x y : E) ->
      apply (addV domain x y) ==
      addV codomain (apply x) (apply y)
    map-scale-vector :
      (a : K) ->
      (x : E) ->
      apply (scaleV domain a x) ==
      scaleV codomain (mapScalar scalarHom a) (apply x)
    continuous-map :
      (x : E) ->
      (epsilon : R) ->
      Positive reals epsilon ->
      Exists R
        (\ delta ->
          Both
            (Positive reals delta)
            ((y : E) ->
              StrictLess reals (distanceV domain y x) delta ->
              StrictLess reals
                (distanceV codomain (apply y) (apply x))
                epsilon))

open ContinuousSemilinearMap

Subset : Set -> Set1
Subset X =
  X -> Set

Image :
  {K K2 R E F : Set}
  {reals : CompleteOrderedField R}
  {sourceScalars : NontriviallyNormedField K R reals}
  {targetScalars : NontriviallyNormedField K2 R reals}
  {scalarHom : IsometricRingHom sourceScalars targetScalars}
  {domain : NormedSpace K R E reals sourceScalars}
  {codomain : NormedSpace K2 R F reals targetScalars} ->
  ContinuousSemilinearMap scalarHom domain codomain ->
  Subset E ->
  Subset F
Image {E = E} linear U y =
  Exists E
    (\ x ->
      Both
        (U x)
        (apply linear x == y))

IsOpen :
  {K R V : Set}
  {reals : CompleteOrderedField R}
  {scalars : NontriviallyNormedField K R reals} ->
  NormedSpace K R V reals scalars ->
  Subset V ->
  Set
IsOpen {R = R} {V = V} {reals = reals} space U =
  (x : V) ->
  U x ->
  Exists R
    (\ radius ->
      Both
        (Positive reals radius)
        ((y : V) ->
          StrictLess reals (distanceV space y x) radius ->
          U y))

Surjective :
  {K K2 R E F : Set}
  {reals : CompleteOrderedField R}
  {sourceScalars : NontriviallyNormedField K R reals}
  {targetScalars : NontriviallyNormedField K2 R reals}
  {scalarHom : IsometricRingHom sourceScalars targetScalars}
  {domain : NormedSpace K R E reals sourceScalars}
  {codomain : NormedSpace K2 R F reals targetScalars} ->
  ContinuousSemilinearMap scalarHom domain codomain ->
  Set
Surjective {E = E} {F = F} linear =
  (y : F) ->
  Exists E (\ x -> apply linear x == y)

IsOpenMap :
  {K K2 R E F : Set}
  {reals : CompleteOrderedField R}
  {sourceScalars : NontriviallyNormedField K R reals}
  {targetScalars : NontriviallyNormedField K2 R reals}
  {scalarHom : IsometricRingHom sourceScalars targetScalars}
  (domain : NormedSpace K R E reals sourceScalars)
  (codomain : NormedSpace K2 R F reals targetScalars) ->
  ContinuousSemilinearMap scalarHom domain codomain ->
  Set1
IsOpenMap domain codomain linear =
  (U : Subset _) ->
  IsOpen domain U ->
  IsOpen codomain (Image linear U)

open-mapping-theorem-functional-analysis : Set1
open-mapping-theorem-functional-analysis =
  (R K K2 E F : Set) ->
  (reals : CompleteOrderedField R) ->
  (sourceScalars : NontriviallyNormedField K R reals) ->
  (targetScalars : NontriviallyNormedField K2 R reals) ->
  (scalarHom : IsometricRingHom sourceScalars targetScalars) ->
  (inverseScalarHom : IsometricRingHom targetScalars sourceScalars) ->
  InverseRingHomPair scalarHom inverseScalarHom ->
  (domain : NormedSpace K R E reals sourceScalars) ->
  (codomain : NormedSpace K2 R F reals targetScalars) ->
  Complete domain ->
  Complete codomain ->
  (linear : ContinuousSemilinearMap scalarHom domain codomain) ->
  Surjective linear ->
  IsOpenMap domain codomain linear
