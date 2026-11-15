-- Statement-only formalization of the thousand-theorems corpus artifact Q643826,
-- "Slutsky's theorem": a continuous function of variables converging respectively
-- in distribution and in probability to a constant converges in distribution.
-- This file contains no proof.

{-# OPTIONS --safe #-}

module Q643826_slutsky_s_theorem where

open import Agda.Builtin.Equality renaming (_≡_ to _==_)
open import Agda.Builtin.Nat using (Nat)
open import Support.SlutskyProbabilityBase

open CompleteOrderedField
open RealPresentation
open TopologicalSpace
open Filter
open Measure
open ProbabilitySpace

record Pair (A B : Set) : Set where
  constructor pair
  field
    first-pair  : A
    second-pair : B

record SeminormedAddCommGroup
  {R : Set}
  (real : RealPresentation R)
  (A : Set) : Set1 where
  field
    zeroA :
      A
    addA :
      A -> A -> A
    negateA :
      A -> A
    normA :
      A -> R

    add-commutativeA :
      (x y : A) ->
      addA x y == addA y x
    add-associativeA :
      (x y z : A) ->
      addA (addA x y) z == addA x (addA y z)
    add-zeroA :
      (x : A) ->
      addA x zeroA == x
    add-inverseA :
      (x : A) ->
      addA x (negateA x) == zeroA

    norm-nonnegativeA :
      (x : A) ->
      lessOrEqualR (reals real) (zeroR (reals real)) (normA x)
    norm-zeroA :
      normA zeroA == zeroR (reals real)
    norm-negateA :
      (x : A) ->
      normA (negateA x) == normA x
    norm-triangleA :
      (x y : A) ->
      lessOrEqualR (reals real)
        (normA (addA x y))
        (addR (reals real) (normA x) (normA y))

open SeminormedAddCommGroup

subtractA :
  {R A : Set} ->
  {real : RealPresentation R} ->
  SeminormedAddCommGroup real A ->
  A ->
  A ->
  A
subtractA group x y =
  addA group x (negateA group y)

NormMetricOpen :
  {R A : Set} ->
  {real : RealPresentation R} ->
  SeminormedAddCommGroup real A ->
  Predicate A ->
  Set
NormMetricOpen {R = R} {A = A} {real = real} group U =
  (x : A) ->
  U x ->
  Exists R
    (\ radius ->
      Both
        (Positive (reals real) radius)
        (Subset
          (\ y ->
            StrictLess (reals real)
              (normA group (subtractA group y x))
              radius)
          U))

record NormTopologyPresentation
  {R A : Set}
  {real : RealPresentation R}
  (group : SeminormedAddCommGroup real A)
  (topology : TopologicalSpace A) : Set1 where
  field
    topology-is-norm-metric :
      (U : Predicate A) ->
      Iff
        (openSet topology U)
        (NormMetricOpen group U)

record SecondCountableTopology
  {A : Set}
  (topology : TopologicalSpace A) : Set1 where
  field
    countable-basis :
      Nat -> Predicate A
    basis-open :
      (n : Nat) ->
      openSet topology (countable-basis n)
    basis-refines-open :
      (U : Predicate A) ->
      openSet topology U ->
      (x : A) ->
      U x ->
      Exists Nat
        (\ n ->
          Both
            (countable-basis n x)
            (Subset (countable-basis n) U))

record CountablyGeneratedFilter
  {I : Set}
  (sourceFilter : Filter I) : Set1 where
  field
    filter-basis :
      Nat -> Predicate I
    basis-eventually :
      (n : Nat) ->
      eventually sourceFilter (filter-basis n)
    basis-generates :
      (P : Predicate I) ->
      eventually sourceFilter P ->
      Exists Nat
        (\ n ->
          Subset (filter-basis n) P)

record ProductNeighborhood
  {A B C : Set}
  (sourceA : TopologicalSpace A)
  (sourceB : TopologicalSpace B)
  (g : Pair A B -> C)
  (U : Predicate C)
  (x : A)
  (y : B) : Set2 where
  field
    left-neighborhood :
      Predicate A
    right-neighborhood :
      Predicate B
    left-open :
      openSet sourceA left-neighborhood
    right-open :
      openSet sourceB right-neighborhood
    left-contains :
      left-neighborhood x
    right-contains :
      right-neighborhood y
    image-contained :
      (x' : A) ->
      left-neighborhood x' ->
      (y' : B) ->
      right-neighborhood y' ->
      U (g (pair x' y'))

ContinuousPair :
  {A B C : Set} ->
  TopologicalSpace A ->
  TopologicalSpace B ->
  TopologicalSpace C ->
  (Pair A B -> C) ->
  Set2
ContinuousPair sourceA sourceB target g =
  (U : Predicate _) ->
  openSet target U ->
  (x : _) ->
  (y : _) ->
  U (g (pair x y)) ->
  ProductNeighborhood sourceA sourceB g U x y

TendstoInMeasureConstant :
  {R I A E : Set} ->
  (real : RealPresentation R) ->
  (sourceEvents : SigmaAlgebra A) ->
  (sourceProbability : ProbabilitySpace real sourceEvents) ->
  (group : SeminormedAddCommGroup real E) ->
  Filter I ->
  (I -> A -> E) ->
  E ->
  Set
TendstoInMeasureConstant
  {R = R}
  real
  sourceEvents
  sourceProbability
  group
  sourceFilter
  Y
  c =
  (epsilon : R) ->
  Positive (reals real) epsilon ->
  TendstoReal (reals real) sourceFilter
    (\ i ->
      outerMass (probabilityMeasure sourceProbability)
        (\ omega ->
          lessOrEqualR (reals real)
            epsilon
            (normA group (subtractA group (Y i omega) c))))
    (zeroR (reals real))

slutsky-s-theorem : Set2
slutsky-s-theorem =
  (R I E EPrime F OmegaPrime OmegaDoublePrime : Set) ->
  (real : RealPresentation R) ->
  (sourceEvents : SigmaAlgebra OmegaDoublePrime) ->
  (limitEvents : SigmaAlgebra OmegaPrime) ->
  (topologyE : TopologicalSpace E) ->
  (eventsE : SigmaAlgebra E) ->
  (groupE : SeminormedAddCommGroup real E) ->
  NormTopologyPresentation groupE topologyE ->
  SecondCountableTopology topologyE ->
  BorelSpace topologyE eventsE ->
  (topologyEPrime : TopologicalSpace EPrime) ->
  (eventsEPrime : SigmaAlgebra EPrime) ->
  (groupEPrime : SeminormedAddCommGroup real EPrime) ->
  NormTopologyPresentation groupEPrime topologyEPrime ->
  SecondCountableTopology topologyEPrime ->
  BorelSpace topologyEPrime eventsEPrime ->
  (topologyF : TopologicalSpace F) ->
  (eventsF : SigmaAlgebra F) ->
  BorelSpace topologyF eventsF ->
  (sourceFilter : Filter I) ->
  CountablyGeneratedFilter sourceFilter ->
  (sourceProbability :
    ProbabilitySpace real sourceEvents) ->
  (limitProbability :
    ProbabilitySpace real limitEvents) ->
  (X : I -> OmegaDoublePrime -> E) ->
  (Y : I -> OmegaDoublePrime -> EPrime) ->
  (Z : OmegaPrime -> E) ->
  (c : EPrime) ->
  (g : Pair E EPrime -> F) ->
  ContinuousPair topologyE topologyEPrime topologyF g ->
  TendstoInDistribution
    real
    (\ _ -> OmegaDoublePrime)
    (\ _ -> sourceEvents)
    topologyE
    eventsE
    X
    sourceFilter
    Z
    limitEvents
    (\ _ -> sourceProbability)
    limitProbability ->
  TendstoInMeasureConstant
    real
    sourceEvents
    sourceProbability
    groupEPrime
    sourceFilter
    Y
    c ->
  ((i : I) ->
    AEMeasurable
      sourceEvents
      eventsEPrime
      (probabilityMeasure sourceProbability)
      (Y i)) ->
  TendstoInDistribution
    real
    (\ _ -> OmegaDoublePrime)
    (\ _ -> sourceEvents)
    topologyF
    eventsF
    (\ i omega -> g (pair (X i omega) (Y i omega)))
    sourceFilter
    (\ omega -> g (pair (Z omega) c))
    limitEvents
    (\ _ -> sourceProbability)
    limitProbability
