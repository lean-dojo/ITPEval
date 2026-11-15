-- Statement-only formalization of thousand-theorems corpus artifact Q966837,
-- "Cramér–Wold theorem": convergence in distribution of finite-dimensional
-- real inner-product-space-valued random variables is equivalent to convergence
-- in distribution of every scalar inner-product projection. This file contains no proof.

{-# OPTIONS --safe #-}

module Q966837_cramer_wold_theorem where

open import Agda.Builtin.Equality renaming (_≡_ to _==_)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Support.SlutskyProbabilityBase

open CompleteOrderedField
open RealPresentation
open Filter
open ProbabilitySpace

record Iff₂ (A B : Set2) : Set2 where
  constructor equivalence₂
  field
    forward₂  : A -> B
    backward₂ : B -> A

record AtTopFilter (sourceFilter : Filter Nat) : Set1 where
  field
    eventually-at-top :
      (P : Predicate Nat) ->
      Iff
        (eventually sourceFilter P)
        (Exists Nat
          (\ cutoff ->
            (n : Nat) ->
            cutoff <=N n ->
            P n))

record NormedRealInnerProductSpace
  (R E : Set)
  (real : RealPresentation R) : Set1 where
  field
    zeroE :
      E
    addE :
      E -> E -> E
    negateE :
      E -> E
    scaleE :
      R -> E -> E
    normE :
      E -> R
    innerE :
      E -> E -> R

    add-commutativeE :
      (x y : E) ->
      addE x y == addE y x
    add-associativeE :
      (x y z : E) ->
      addE (addE x y) z == addE x (addE y z)
    add-zeroE :
      (x : E) ->
      addE x zeroE == x
    add-inverseE :
      (x : E) ->
      addE x (negateE x) == zeroE

    scale-oneE :
      (x : E) ->
      scaleE (oneR (reals real)) x == x
    scale-zeroE :
      (x : E) ->
      scaleE (zeroR (reals real)) x == zeroE
    scale-associativeE :
      (a b : R) ->
      (x : E) ->
      scaleE (multiplyR (reals real) a b) x ==
      scaleE a (scaleE b x)
    scale-add-scalarsE :
      (a b : R) ->
      (x : E) ->
      scaleE (addR (reals real) a b) x ==
      addE (scaleE a x) (scaleE b x)
    scale-add-vectorsE :
      (a : R) ->
      (x y : E) ->
      scaleE a (addE x y) ==
      addE (scaleE a x) (scaleE a y)

    inner-add-left :
      (x y z : E) ->
      innerE (addE x y) z ==
      addR (reals real) (innerE x z) (innerE y z)
    inner-scale-left :
      (a : R) ->
      (x y : E) ->
      innerE (scaleE a x) y ==
      multiplyR (reals real) a (innerE x y)
    inner-symmetric :
      (x y : E) ->
      innerE x y == innerE y x
    inner-nonnegative :
      (x : E) ->
      lessOrEqualR (reals real)
        (zeroR (reals real))
        (innerE x x)
    inner-definite :
      (x : E) ->
      innerE x x == zeroR (reals real) ->
      x == zeroE

    norm-nonnegative :
      (x : E) ->
      lessOrEqualR (reals real)
        (zeroR (reals real))
        (normE x)
    norm-square :
      (x : E) ->
      multiplyR (reals real) (normE x) (normE x) ==
      innerE x x
    norm-triangle :
      (x y : E) ->
      lessOrEqualR (reals real)
        (normE (addE x y))
        (addR (reals real) (normE x) (normE y))
    norm-scale :
      (a : R) ->
      (x : E) ->
      normE (scaleE a x) ==
      multiplyR (reals real)
        (absoluteR (reals real) a)
        (normE x)

open NormedRealInnerProductSpace

subtractE :
  {R E : Set} ->
  {real : RealPresentation R} ->
  NormedRealInnerProductSpace R E real ->
  E ->
  E ->
  E
subtractE space x y =
  addE space x (negateE space y)

distanceE :
  {R E : Set} ->
  {real : RealPresentation R} ->
  NormedRealInnerProductSpace R E real ->
  E ->
  E ->
  R
distanceE space x y =
  normE space (subtractE space x y)

NormMetricOpen :
  {R E : Set} ->
  {real : RealPresentation R} ->
  NormedRealInnerProductSpace R E real ->
  Predicate E ->
  Set
NormMetricOpen {R = R} {E = E} {real = real} space U =
  (x : E) ->
  U x ->
  Exists R
    (\ radius ->
      Both
        (Positive (reals real) radius)
        (Subset
          (\ y ->
            StrictLess (reals real)
              (distanceE space y x)
              radius)
          U))

record NormTopologyPresentation
  {R E : Set}
  {real : RealPresentation R}
  (space : NormedRealInnerProductSpace R E real)
  (topology : TopologicalSpace E) : Set1 where
  field
    topology-is-norm-metric :
      (U : Predicate E) ->
      Iff
        (openSet topology U)
        (NormMetricOpen space U)

data Fin : Nat -> Set where
  fzero : {n : Nat} -> Fin (suc n)
  fsuc  : {n : Nat} -> Fin n -> Fin (suc n)

Vector :
  Set ->
  Nat ->
  Set
Vector R n =
  Fin n -> R

VectorEqual :
  {R : Set} ->
  {n : Nat} ->
  Vector R n ->
  Vector R n ->
  Set
VectorEqual {n = n} x y =
  (i : Fin n) ->
  x i == y i

sumVector :
  {R : Set} ->
  CompleteOrderedField R ->
  (n : Nat) ->
  Vector R n ->
  R
sumVector reals zero terms =
  zeroR reals
sumVector reals (suc n) terms =
  addR reals
    (terms fzero)
    (sumVector reals n (\ i -> terms (fsuc i)))

record FiniteDimensional
  {R E : Set}
  {real : RealPresentation R}
  (space : NormedRealInnerProductSpace R E real) : Set1 where
  field
    dimension :
      Nat
    toCoordinates :
      E ->
      Vector R dimension
    fromCoordinates :
      Vector R dimension ->
      E
    coordinates-after-vector :
      (coordinates : Vector R dimension) ->
      VectorEqual
        (toCoordinates (fromCoordinates coordinates))
        coordinates
    vector-after-coordinates :
      (x : E) ->
      fromCoordinates (toCoordinates x) == x
    coordinates-add :
      (x y : E) ->
      VectorEqual
        (toCoordinates (addE space x y))
        (\ i ->
          addR (reals real)
            (toCoordinates x i)
            (toCoordinates y i))
    coordinates-scale :
      (a : R) ->
      (x : E) ->
      VectorEqual
        (toCoordinates (scaleE space a x))
        (\ i ->
          multiplyR (reals real) a (toCoordinates x i))
    coordinates-orthonormal :
      (x y : E) ->
      innerE space x y ==
      sumVector (reals real) dimension
        (\ i ->
          multiplyR (reals real)
            (toCoordinates x i)
            (toCoordinates y i))

cramer-wold-theorem : Set2
cramer-wold-theorem =
  (R E Omega OmegaPrime : Set) ->
  (real : RealPresentation R) ->
  (space : NormedRealInnerProductSpace R E real) ->
  FiniteDimensional space ->
  (topologyE : TopologicalSpace E) ->
  NormTopologyPresentation space topologyE ->
  (eventsE : SigmaAlgebra E) ->
  BorelSpace topologyE eventsE ->
  (sourceEvents : SigmaAlgebra Omega) ->
  (limitEvents : SigmaAlgebra OmegaPrime) ->
  (sourceProbability :
    ProbabilitySpace real sourceEvents) ->
  (limitProbability :
    ProbabilitySpace real limitEvents) ->
  (sourceFilter : Filter Nat) ->
  AtTopFilter sourceFilter ->
  (X : Nat -> Omega -> E) ->
  (XPrime : OmegaPrime -> E) ->
  AEMeasurable
    limitEvents
    eventsE
    (probabilityMeasure limitProbability)
    XPrime ->
  ((n : Nat) ->
    AEMeasurable
      sourceEvents
      eventsE
      (probabilityMeasure sourceProbability)
      (X n)) ->
  Iff₂
    (TendstoInDistribution
      real
      (\ _ -> Omega)
      (\ _ -> sourceEvents)
      topologyE
      eventsE
      X
      sourceFilter
      XPrime
      limitEvents
      (\ _ -> sourceProbability)
      limitProbability)
    ((t : E) ->
      TendstoInDistribution
        real
        (\ _ -> Omega)
        (\ _ -> sourceEvents)
        (topologyR real)
        (borelR real)
        (\ n omega -> innerE space (X n omega) t)
        sourceFilter
        (\ omega -> innerE space (XPrime omega) t)
        limitEvents
        (\ _ -> sourceProbability)
        limitProbability)
