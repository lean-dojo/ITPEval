-- Statement-only formalization of thousand-theorems corpus artifact Q2275191,
-- "Lebesgue differentiation theorem": along a Vitali family, normalized set
-- lower integrals of an almost-everywhere measurable nonnegative function
-- converge to its value almost everywhere. This file contains no proof.

{-# OPTIONS --safe #-}

module Q2275191_lebesgue_differentiation_theorem where

open import Agda.Builtin.Equality renaming (_≡_ to _==_)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.List using (List)
open import Q1067156X_bounded_convergence_theorem

open CompleteOrderedField
open SigmaAlgebra
open ExtendedNonnegativeReals
open Measure
open NonnegativeReal
open Filter

infix 4 _!=1_

_!=1_ :
  {A : Set1} ->
  A ->
  A ->
  Set1
x !=1 y =
  Not1 (x == y)

record BothLarge (A : Set) (B : Set1) : Set1 where
  constructor both-large
  field
    small-part : A
    large-part : B

record ExistsLarge (A : Set) (P : A -> Set1) : Set1 where
  constructor witness-large
  field
    large-value    : A
    large-property : P large-value

record ExistsHigh (A : Set1) (P : A -> Set) : Set1 where
  constructor witness-high
  field
    high-value    : A
    high-property : P high-value

record PseudoMetricSpace
  (R A : Set)
  (reals : CompleteOrderedField R) : Set1 where
  field
    distance :
      A -> A -> R
    distance-nonnegative :
      (x y : A) ->
      lessOrEqualR reals (zeroR reals) (distance x y)
    distance-self :
      (x : A) ->
      distance x x == zeroR reals
    distance-symmetric :
      (x y : A) ->
      distance x y == distance y x
    distance-triangle :
      (x y z : A) ->
      lessOrEqualR reals
        (distance x z)
        (addR reals (distance x y) (distance y z))

open PseudoMetricSpace

ClosedBall :
  {R A : Set} ->
  {reals : CompleteOrderedField R} ->
  PseudoMetricSpace R A reals ->
  A ->
  R ->
  Predicate A
ClosedBall {reals = reals} metric center radius x =
  lessOrEqualR reals (distance metric x center) radius

OpenBall :
  {R A : Set} ->
  {reals : CompleteOrderedField R} ->
  PseudoMetricSpace R A reals ->
  A ->
  R ->
  Predicate A
OpenBall {reals = reals} metric center radius x =
  StrictLess reals (distance metric x center) radius

MetricOpen :
  {R A : Set} ->
  {reals : CompleteOrderedField R} ->
  PseudoMetricSpace R A reals ->
  Predicate A ->
  Set
MetricOpen {R = R} {A = A} {reals = reals} metric U =
  (x : A) ->
  U x ->
  Exists R
    (\ radius ->
      Both
        (Positive reals radius)
        (Subset (OpenBall metric x radius) U))

InteriorNonempty :
  {R A : Set} ->
  {reals : CompleteOrderedField R} ->
  PseudoMetricSpace R A reals ->
  Predicate A ->
  Set
InteriorNonempty {R = R} {A = A} {reals = reals} metric S =
  Exists A
    (\ x ->
      Exists R
        (\ radius ->
          Both
            (Positive reals radius)
            (Subset (OpenBall metric x radius) S)))

record SecondCountableMetric
  {R A : Set}
  {reals : CompleteOrderedField R}
  (metric : PseudoMetricSpace R A reals) : Set2 where
  field
    countable-basis :
      Nat -> Predicate A
    basis-open :
      (n : Nat) ->
      MetricOpen metric (countable-basis n)
    basis-refines :
      (U : Predicate A) ->
      MetricOpen metric U ->
      (x : A) ->
      U x ->
      Exists Nat
        (\ n ->
          Both
            (countable-basis n x)
            (Subset (countable-basis n) U))

data BorelGenerated
  {R A : Set}
  {reals : CompleteOrderedField R}
  (metric : PseudoMetricSpace R A reals) :
  Predicate A -> Set1 where

  borel-open :
    {U : Predicate A} ->
    MetricOpen metric U ->
    BorelGenerated metric U

  borel-empty :
    BorelGenerated metric emptySet

  borel-complement :
    {S : Predicate A} ->
    BorelGenerated metric S ->
    BorelGenerated metric (complement S)

  borel-countable-union :
    (sets : Nat -> Predicate A) ->
    ((n : Nat) -> BorelGenerated metric (sets n)) ->
    BorelGenerated metric (countableUnion sets)

  borel-congruent :
    {S T : Predicate A} ->
    ((x : A) -> Iff (S x) (T x)) ->
    BorelGenerated metric S ->
    BorelGenerated metric T

record BorelSpace
  {R A : Set}
  {reals : CompleteOrderedField R}
  (metric : PseudoMetricSpace R A reals)
  (events : SigmaAlgebra A) : Set2 where
  field
    borel-measurable :
      (S : Predicate A) ->
      BorelGenerated metric S ->
      measurable events S
    measurable-borel :
      (S : Predicate A) ->
      measurable events S ->
      BorelGenerated metric S

IsLocallyFiniteMeasure :
  {R M A : Set} ->
  {reals : CompleteOrderedField R} ->
  {events : SigmaAlgebra A} ->
  {extended : ExtendedNonnegativeReals R M reals} ->
  PseudoMetricSpace R A reals ->
  Measure extended events ->
  Set
IsLocallyFiniteMeasure {R = R} {A = A} {reals = reals}
  {extended = extended} metric measure =
  (x : A) ->
  Exists R
    (\ radius ->
      Both
        (Positive reals radius)
        (outerMass measure (ClosedBall metric x radius) !=
          infinityM extended))

record IndexedSimpleBelowM
  {A R M : Set}
  {reals : CompleteOrderedField R}
  (events : SigmaAlgebra A)
  (extended : ExtendedNonnegativeReals R M reals)
  (f : A -> M) : Set where
  field
    simple-cutoff :
      Nat
    simple-index :
      A -> Nat
    simple-values :
      Nat -> M
    simple-index-within :
      (x : A) ->
      simple-index x <=N simple-cutoff
    simple-fiber-measurable :
      (i : Nat) ->
      i <=N simple-cutoff ->
      measurable events (\ x -> simple-index x == i)
    simple-below :
      (x : A) ->
      lessOrEqualM extended
        (simple-values (simple-index x))
        (f x)

open IndexedSimpleBelowM

indexedSimpleIntegralM :
  {A R M : Set} ->
  {reals : CompleteOrderedField R} ->
  {events : SigmaAlgebra A} ->
  (extended : ExtendedNonnegativeReals R M reals) ->
  (measure : Measure extended events) ->
  {f : A -> M} ->
  IndexedSimpleBelowM events extended f ->
  M
indexedSimpleIntegralM extended measure simple =
  sumThroughM extended
    (\ i ->
      multiplyM extended
        (simple-values simple i)
        (outerMass measure
          (\ x -> simple-index simple x == i)))
    (simple-cutoff simple)

record SimpleIntegralCandidateM
  {A R M : Set}
  {reals : CompleteOrderedField R}
  {events : SigmaAlgebra A}
  (extended : ExtendedNonnegativeReals R M reals)
  (measure : Measure extended events)
  (f : A -> M)
  (candidate : M) : Set where
  field
    candidate-simple :
      IndexedSimpleBelowM events extended f
    candidate-equation :
      candidate ==
      indexedSimpleIntegralM extended measure candidate-simple

canonicalLIntegralM :
  {A R M : Set} ->
  {reals : CompleteOrderedField R} ->
  {events : SigmaAlgebra A} ->
  (extended : ExtendedNonnegativeReals R M reals) ->
  Measure extended events ->
  (A -> M) ->
  M
canonicalLIntegralM extended measure f =
  supremumM extended
    (\ candidate ->
      SimpleIntegralCandidateM extended measure f candidate)

MeasurableOrder :
  {A V : Set} ->
  (events : SigmaAlgebra A) ->
  (V -> V -> Set) ->
  (A -> V) ->
  Set
MeasurableOrder events le f =
  (ray : OrderRay _) ->
  measurable events (\ x -> RayContains le ray (f x))

AEMeasurableOrder :
  {A R M V : Set} ->
  {reals : CompleteOrderedField R} ->
  {extended : ExtendedNonnegativeReals R M reals} ->
  (events : SigmaAlgebra A) ->
  Measure extended events ->
  (V -> V -> Set) ->
  (A -> V) ->
  Set
AEMeasurableOrder {A = A} events measure le f =
  Exists (A -> _)
    (\ representative ->
      Both
        (MeasurableOrder events le representative)
        (AlmostEverywhere measure
          (\ x -> f x == representative x)))

record MeasureRestriction
  {A R M : Set}
  {reals : CompleteOrderedField R}
  (events : SigmaAlgebra A)
  (extended : ExtendedNonnegativeReals R M reals) : Set2 where
  field
    restrict :
      Measure extended events ->
      Predicate A ->
      Measure extended events
    restrict-on-measurable :
      (measure : Measure extended events) ->
      (S : Predicate A) ->
      measurable events S ->
      (T : Predicate A) ->
      outerMass (restrict measure S) T ==
      outerMass measure (intersection T S)

open MeasureRestriction

SetLIntegral :
  {A R M : Set} ->
  {reals : CompleteOrderedField R} ->
  {events : SigmaAlgebra A} ->
  {extended : ExtendedNonnegativeReals R M reals} ->
  MeasureRestriction events extended ->
  Measure extended events ->
  Predicate A ->
  (A -> M) ->
  M
SetLIntegral {extended = extended} restrictions measure S f =
  canonicalLIntegralM extended (restrict restrictions measure S) f

record ENNRealReciprocal
  {R M : Set}
  {reals : CompleteOrderedField R}
  (extended : ExtendedNonnegativeReals R M reals) : Set1 where
  field
    reciprocalM :
      M -> M
    reciprocal-zero :
      reciprocalM (zeroM extended) == infinityM extended
    reciprocal-infinity :
      reciprocalM (infinityM extended) == zeroM extended
    reciprocal-finite-zero :
      (x : NonnegativeReal reals) ->
      realValue x == zeroR reals ->
      reciprocalM (finiteNN extended x) == infinityM extended
    reciprocal-finite-positive :
      (x : NonnegativeReal reals) ->
      realValue x != zeroR reals ->
      Exists (NonnegativeReal reals)
        (\ inverse ->
          Both
            (realValue inverse ==
              reciprocalR reals (realValue x))
            (reciprocalM (finiteNN extended x) ==
              finiteNN extended inverse))

open ENNRealReciprocal

divideM :
  {R M : Set} ->
  {reals : CompleteOrderedField R} ->
  (extended : ExtendedNonnegativeReals R M reals) ->
  ENNRealReciprocal extended ->
  M ->
  M ->
  M
divideM extended reciprocal x y =
  multiplyM extended x (reciprocalM reciprocal y)

SetFamily :
  Set ->
  Set1
SetFamily A =
  Predicate A -> Set

SelectedUnion :
  {A I : Set} ->
  (I -> Predicate A) ->
  Predicate A
SelectedUnion {I = I} selected x =
  Exists I (\ i -> selected i x)

SetDifference :
  {A : Set} ->
  Predicate A ->
  Predicate A ->
  Predicate A
SetDifference S T x =
  Both (S x) (Not (T x))

record CoveringSelection
  {A R M : Set}
  {reals : CompleteOrderedField R}
  {events : SigmaAlgebra A}
  {extended : ExtendedNonnegativeReals R M reals}
  (measure : Measure extended events)
  (S : Predicate A)
  (family : A -> SetFamily A) : Set1 where
  field
    selected-index :
      Set
    selected-center :
      selected-index -> A
    selected-region :
      selected-index -> Predicate A
    selected-centers-in-S :
      (i : selected-index) ->
      S (selected-center i)
    selected-pairwise-disjoint :
      (i j : selected-index) ->
      i != j ->
      (x : A) ->
      selected-region i x ->
      selected-region j x ->
      Bottom
    selected-from-family :
      (i : selected-index) ->
      family (selected-center i) (selected-region i)
    covers-almost-all :
      outerMass measure
        (SetDifference S (SelectedUnion selected-region)) ==
      zeroM extended

ExistsCovering :
  {A R M : Set}
  {reals : CompleteOrderedField R}
  {events : SigmaAlgebra A}
  {extended : ExtendedNonnegativeReals R M reals}
  (measure : Measure extended events)
  (S : Predicate A)
  (family : A -> SetFamily A) ->
  Set1
ExistsCovering measure S family =
  CoveringSelection measure S family

record Filter1 (I : Set1) : Set2 where
  field
    eventually1 :
      (I -> Set) -> Set1
    eventually-whole1 :
      eventually1 (\ _ -> Top)
    eventually-upward1 :
      (P Q : I -> Set) ->
      eventually1 P ->
      ((i : I) -> P i -> Q i) ->
      eventually1 Q
    eventually-intersection1 :
      (P Q : I -> Set) ->
      eventually1 P ->
      eventually1 Q ->
      eventually1 (\ i -> Both (P i) (Q i))

open Filter1

FilterAtSmall :
  {R A : Set} ->
  {reals : CompleteOrderedField R} ->
  (metric : PseudoMetricSpace R A reals) ->
  (setsAt : A -> SetFamily A) ->
  A ->
  (Predicate A -> Set) ->
  Set1
FilterAtSmall {R = R} {reals = reals} metric setsAt x P =
  ExistsLarge R
    (\ radius ->
      BothLarge
        (Positive reals radius)
        ((S : Predicate _) ->
          setsAt x S ->
          Subset S (ClosedBall metric x radius) ->
          P S))

record VitaliFamily
  {R M A : Set}
  {reals : CompleteOrderedField R}
  (metric : PseudoMetricSpace R A reals)
  (events : SigmaAlgebra A)
  (extended : ExtendedNonnegativeReals R M reals)
  (measure : Measure extended events) : Set3 where
  field
    setsAt :
      A -> SetFamily A
    sets-measurable :
      (x : A) ->
      (S : Predicate A) ->
      setsAt x S ->
      measurable events S
    sets-interior-nonempty :
      (x : A) ->
      (S : Predicate A) ->
      setsAt x S ->
      InteriorNonempty metric S
    nontrivial :
      (x : A) ->
      (radius : R) ->
      Positive reals radius ->
      ExistsHigh (Predicate A)
        (\ S ->
          Both
            (setsAt x S)
            (Subset S (ClosedBall metric x radius)))
    covering :
      (S : Predicate A) ->
      (family : A -> SetFamily A) ->
      ((x : A) ->
        S x ->
        (T : Predicate A) ->
        family x T ->
        setsAt x T) ->
      ((x : A) ->
        S x ->
        (radius : R) ->
        Positive reals radius ->
        ExistsHigh (Predicate A)
          (\ T ->
            Both
              (family x T)
              (Subset T (ClosedBall metric x radius)))) ->
      ExistsCovering measure S family
    filterAt :
      A -> Filter1 (Predicate A)
    filterAt-small :
      (x : A) ->
      (P : Predicate A -> Set) ->
      Iff1
        (eventually1 (filterAt x) P)
        (FilterAtSmall metric setsAt x P)

open VitaliFamily

TendstoM1 :
  {I R M : Set} ->
  {reals : CompleteOrderedField R} ->
  (extended : ExtendedNonnegativeReals R M reals) ->
  Filter1 (Predicate I) ->
  (Predicate I -> M) ->
  M ->
  Set1
TendstoM1 extended source-filter function limit =
  (rays : List (OrderRay _)) ->
  BasicContains (lessOrEqualM extended) rays limit ->
  eventually1 source-filter
    (\ i ->
      BasicContains (lessOrEqualM extended) rays (function i))

record AlmostEverywhereLarge
  {A R M : Set}
  {reals : CompleteOrderedField R}
  {events : SigmaAlgebra A}
  {extended : ExtendedNonnegativeReals R M reals}
  (measure : Measure extended events)
  (property : A -> Set1) : Set1 where
  field
    exceptional-set :
      Predicate A
    exceptional-null :
      outerMass measure exceptional-set == zeroM extended
    property-off-exceptional :
      (x : A) ->
      Not (exceptional-set x) ->
      property x

lebesgue-differentiation-theorem : Set3
lebesgue-differentiation-theorem =
  (A R M : Set) ->
  (reals : CompleteOrderedField R) ->
  RealNumberPresentation reals ->
  (metric : PseudoMetricSpace R A reals) ->
  SecondCountableMetric metric ->
  (events : SigmaAlgebra A) ->
  BorelSpace metric events ->
  (extended : ExtendedNonnegativeReals R M reals) ->
  ENNRealPresentation extended ->
  (reciprocal : ENNRealReciprocal extended) ->
  (measure : Measure extended events) ->
  IsLocallyFiniteMeasure metric measure ->
  (restrictions : MeasureRestriction events extended) ->
  (vitali : VitaliFamily metric events extended measure) ->
  (f : A -> M) ->
  AEMeasurableOrder events measure (lessOrEqualM extended) f ->
  canonicalLIntegralM extended measure f != infinityM extended ->
  AlmostEverywhereLarge measure
    (\ x ->
      TendstoM1 extended (filterAt vitali x)
        (\ S ->
          divideM extended reciprocal
            (SetLIntegral restrictions measure S f)
            (outerMass measure S))
        (f x))
