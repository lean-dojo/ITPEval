-- Statement-only formalization of thousand-theorems corpus artifact Q5437947,
-- "Fatou–Lebesgue theorem": Fatou's inequality for lower Lebesgue integrals
-- of measurable extended-nonnegative-real-valued sequences. This file contains
-- no proof.

{-# OPTIONS --safe #-}

module Q5437947_fatou_lebesgue_theorem where

open import Agda.Builtin.Equality renaming (_≡_ to _==_)
open import Agda.Builtin.Nat using (Nat)
open import Support.Q1067156X_bounded_convergence_theorem

open CompleteOrderedField
open ExtendedNonnegativeReals
open SigmaAlgebra
open Measure
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

tailInfimumM :
  {R M : Set} ->
  {reals : CompleteOrderedField R} ->
  (extended : ExtendedNonnegativeReals R M reals) ->
  (Nat -> M) ->
  Nat ->
  M
tailInfimumM extended sequence cutoff =
  supremumM extended
    (\ lower ->
      (n : Nat) ->
      cutoff <=N n ->
      lessOrEqualM extended lower (sequence n))

sequenceLiminfM :
  {R M : Set} ->
  {reals : CompleteOrderedField R} ->
  (extended : ExtendedNonnegativeReals R M reals) ->
  (Nat -> M) ->
  M
sequenceLiminfM extended sequence =
  supremumM extended
    (\ value ->
      Exists Nat
        (\ cutoff ->
          value == tailInfimumM extended sequence cutoff))

fatou-lebesgue-theorem : Set2
fatou-lebesgue-theorem =
  (A R M : Set) ->
  (reals : CompleteOrderedField R) ->
  RealNumberPresentation reals ->
  (events : SigmaAlgebra A) ->
  (extended : ExtendedNonnegativeReals R M reals) ->
  ENNRealPresentation extended ->
  (measure : Measure extended events) ->
  (functions : Nat -> A -> M) ->
  ((n : Nat) ->
    MeasurableOrder events
      (lessOrEqualM extended)
      (functions n)) ->
  lessOrEqualM extended
    (canonicalLIntegralM extended measure
      (\ x ->
        sequenceLiminfM extended
          (\ n -> functions n x)))
    (sequenceLiminfM extended
      (\ n ->
        canonicalLIntegralM extended measure (functions n)))
