-- Statement-only formalization of thousand-theorems corpus artifact Q1153584,
-- "Monotone convergence theorem": almost-everywhere monotone sequences of
-- extended-nonnegative-real measurable functions, and almost-everywhere
-- antitone sequences of integrable real functions, have integrals converging
-- to the integral of their pointwise limit. This file contains no proof.

{-# OPTIONS --safe #-}

module Q1153584_monotone_convergence_theorem where

open import Agda.Builtin.Equality renaming (_≡_ to _==_)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.List using (List)
open import Q1067156X_bounded_convergence_theorem

open CompleteOrderedField
open ExtendedNonnegativeReals
open SigmaAlgebra
open Measure
open NonnegativeReal
open ENNRealPresentation

record IndexedSimpleBelowM
  {A R M : Set}
  {reals : CompleteOrderedField R}
  (events : SigmaAlgebra A)
  (extended : ExtendedNonnegativeReals R M reals)
  (f : A -> M) : Set where
  field
    simpleCutoffM :
      Nat
    simpleIndexM :
      A -> Nat
    simpleValuesM :
      Nat -> M
    simpleIndexWithinM :
      (x : A) ->
      simpleIndexM x <=N simpleCutoffM
    simpleFiberMeasurableM :
      (i : Nat) ->
      i <=N simpleCutoffM ->
      measurable events (\ x -> simpleIndexM x == i)
    simplePointwiseBelowM :
      (x : A) ->
      lessOrEqualM extended (simpleValuesM (simpleIndexM x)) (f x)

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
        (simpleValuesM simple i)
        (outerMass measure
          (\ x -> simpleIndexM simple x == i)))
    (simpleCutoffM simple)

record SimpleIntegralCandidateM
  {A R M : Set}
  {reals : CompleteOrderedField R}
  {events : SigmaAlgebra A}
  (extended : ExtendedNonnegativeReals R M reals)
  (measure : Measure extended events)
  (f : A -> M)
  (candidate : M) : Set where
  field
    candidateSimpleM :
      IndexedSimpleBelowM events extended f
    candidateEquationM :
      candidate ==
      indexedSimpleIntegralM extended measure candidateSimpleM

canonicalLIntegralM :
  {A R M : Set} ->
  {reals : CompleteOrderedField R} ->
  {events : SigmaAlgebra A} ->
  (extended : ExtendedNonnegativeReals R M reals) ->
  (measure : Measure extended events) ->
  (A -> M) ->
  M
canonicalLIntegralM extended measure f =
  supremumM extended
    (\ candidate ->
      SimpleIntegralCandidateM extended measure f candidate)

MeasurableOrder :
  {A V : Set} ->
  SigmaAlgebra A ->
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
  (measure : Measure extended events) ->
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

MonotoneSequence :
  {V : Set} ->
  (V -> V -> Set) ->
  (Nat -> V) ->
  Set
MonotoneSequence le sequence =
  (i j : Nat) ->
  i <=N j ->
  le (sequence i) (sequence j)

AntitoneSequence :
  {V : Set} ->
  (V -> V -> Set) ->
  (Nat -> V) ->
  Set
AntitoneSequence le sequence =
  (i j : Nat) ->
  i <=N j ->
  le (sequence j) (sequence i)

SequentialTendstoOrder :
  {V : Set} ->
  (V -> V -> Set) ->
  (Nat -> V) ->
  V ->
  Set
SequentialTendstoOrder le sequence limit =
  (rays : List (OrderRay _)) ->
  BasicContains le rays limit ->
  EventuallyAtTop
    (\ n -> BasicContains le rays (sequence n))

positivePartNN :
  {R : Set} ->
  (reals : CompleteOrderedField R) ->
  R ->
  NonnegativeReal reals
positivePartNN reals x with
  order-total reals (zeroR reals) x
... | left zero-le-x =
  nonnegative-real x zero-le-x
... | right x-le-zero =
  nonnegative-real
    (zeroR reals)
    (order-reflexive reals (zeroR reals))

negativePartNN :
  {R : Set} ->
  (reals : CompleteOrderedField R) ->
  R ->
  NonnegativeReal reals
negativePartNN reals x =
  positivePartNN reals (negateR reals x)

absolutePartNN :
  {R : Set} ->
  (reals : CompleteOrderedField R) ->
  R ->
  NonnegativeReal reals
absolutePartNN reals x =
  nonnegative-real
    (absoluteR reals x)
    (absolute-nonnegative reals x)

toRealM :
  {R M : Set} ->
  {reals : CompleteOrderedField R} ->
  {extended : ExtendedNonnegativeReals R M reals} ->
  ENNRealPresentation extended ->
  M ->
  R
toRealM {reals = reals} presentation x with
  toCanonicalENNReal presentation x
... | finite-ennreal value =
  realValue value
... | infinity-ennreal =
  zeroR reals

RealIntegrable :
  {A R M : Set} ->
  (reals : CompleteOrderedField R) ->
  (events : SigmaAlgebra A) ->
  (extended : ExtendedNonnegativeReals R M reals) ->
  (measure : Measure extended events) ->
  (A -> R) ->
  Set
RealIntegrable reals events extended measure f =
  Both
    (AEMeasurableOrder events measure (lessOrEqualR reals) f)
    (canonicalLIntegralM extended measure
      (\ x -> finiteNN extended (absolutePartNN reals (f x))) !=
      infinityM extended)

realIntegral :
  {A R M : Set} ->
  (reals : CompleteOrderedField R) ->
  {events : SigmaAlgebra A} ->
  (extended : ExtendedNonnegativeReals R M reals) ->
  ENNRealPresentation extended ->
  (measure : Measure extended events) ->
  (A -> R) ->
  R
realIntegral reals extended presentation measure f =
  subtractR reals
    (toRealM presentation
      (canonicalLIntegralM extended measure
        (\ x -> finiteNN extended (positivePartNN reals (f x)))))
    (toRealM presentation
      (canonicalLIntegralM extended measure
        (\ x -> finiteNN extended (negativePartNN reals (f x)))))

lintegral-tendsto-of-tendsto-of-monotone : Set2
lintegral-tendsto-of-tendsto-of-monotone =
  (A R M : Set) ->
  (reals : CompleteOrderedField R) ->
  RealNumberPresentation reals ->
  (events : SigmaAlgebra A) ->
  (extended : ExtendedNonnegativeReals R M reals) ->
  ENNRealPresentation extended ->
  (measure : Measure extended events) ->
  (functions : Nat -> A -> M) ->
  (limit : A -> M) ->
  ((n : Nat) ->
    AEMeasurableOrder events measure
      (lessOrEqualM extended)
      (functions n)) ->
  AlmostEverywhere measure
    (\ x ->
      MonotoneSequence
        (lessOrEqualM extended)
        (\ n -> functions n x)) ->
  AlmostEverywhere measure
    (\ x ->
      SequentialTendstoM extended
        (\ n -> functions n x)
        (limit x)) ->
  SequentialTendstoM extended
    (\ n -> canonicalLIntegralM extended measure (functions n))
    (canonicalLIntegralM extended measure limit)

integral-tendsto-of-tendsto-of-antitone : Set2
integral-tendsto-of-tendsto-of-antitone =
  (A R M : Set) ->
  (reals : CompleteOrderedField R) ->
  RealNumberPresentation reals ->
  (events : SigmaAlgebra A) ->
  (extended : ExtendedNonnegativeReals R M reals) ->
  (presentation : ENNRealPresentation extended) ->
  (measure : Measure extended events) ->
  (functions : Nat -> A -> R) ->
  (limit : A -> R) ->
  ((n : Nat) ->
    RealIntegrable reals events extended measure (functions n)) ->
  RealIntegrable reals events extended measure limit ->
  AlmostEverywhere measure
    (\ x ->
      AntitoneSequence
        (lessOrEqualR reals)
        (\ n -> functions n x)) ->
  AlmostEverywhere measure
    (\ x ->
      SequentialTendstoOrder
        (lessOrEqualR reals)
        (\ n -> functions n x)
        (limit x)) ->
  SequentialTendstoOrder
    (lessOrEqualR reals)
    (\ n ->
      realIntegral reals extended presentation measure (functions n))
    (realIntegral reals extended presentation measure limit)
