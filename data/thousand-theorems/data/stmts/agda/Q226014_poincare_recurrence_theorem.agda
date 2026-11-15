-- Statement-only formalization of thousand-theorems corpus artifact Q226014,
-- "Poincaré recurrence theorem": for a conservative nonsingular self-map,
-- almost every point of a null-measurable set returns to that set infinitely
-- often. This file contains no proof.

{-# OPTIONS --safe #-}

module Q226014_poincare_recurrence_theorem where

open import Agda.Builtin.Equality renaming (_≡_ to _==_)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Support.Q1067156X_bounded_convergence_theorem

open CompleteOrderedField
open SigmaAlgebra
open ExtendedNonnegativeReals
open Measure

preimage :
  {A : Set} ->
  (A -> A) ->
  Predicate A ->
  Predicate A
preimage f S x =
  S (f x)

iterate :
  {A : Set} ->
  (A -> A) ->
  Nat ->
  A ->
  A
iterate f zero x =
  x
iterate f (suc n) x =
  f (iterate f n x)

FrequentlyAtTop :
  {A : Set} ->
  (Nat -> A) ->
  Predicate A ->
  Set
FrequentlyAtTop sequence S =
  (cutoff : Nat) ->
  Exists Nat
    (\ n ->
      Both
        (cutoff <=N n)
        (S (sequence n)))

MeasurableMap :
  {A : Set} ->
  SigmaAlgebra A ->
  (A -> A) ->
  Set1
MeasurableMap events f =
  (S : Predicate _) ->
  measurable events S ->
  measurable events (preimage f S)

record NullMeasurableSet
  {A R M : Set}
  {reals : CompleteOrderedField R}
  {events : SigmaAlgebra A}
  {extended : ExtendedNonnegativeReals R M reals}
  (measure : Measure extended events)
  (S : Predicate A) :
  Set1 where

  field
    measurable-version :
      Predicate A
    measurable-version-is-measurable :
      measurable events measurable-version
    agrees-almost-everywhere :
      AlmostEverywhere measure
        (\ x -> Iff (S x) (measurable-version x))

record QuasiMeasurePreserving
  {A R M : Set}
  {reals : CompleteOrderedField R}
  {events : SigmaAlgebra A}
  {extended : ExtendedNonnegativeReals R M reals}
  (measure : Measure extended events)
  (f : A -> A) :
  Set1 where

  field
    measurable-map :
      MeasurableMap events f
    preimage-of-null-is-null :
      (S : Predicate A) ->
      outerMass measure S == zeroM extended ->
      outerMass measure (preimage f S) == zeroM extended

record Conservative
  {A R M : Set}
  {reals : CompleteOrderedField R}
  {events : SigmaAlgebra A}
  {extended : ExtendedNonnegativeReals R M reals}
  (measure : Measure extended events)
  (f : A -> A) :
  Set1 where

  field
    quasi-measure-preserving :
      QuasiMeasurePreserving measure f
    measurable-positive-set-has-return :
      (S : Predicate A) ->
      measurable events S ->
      Not (outerMass measure S == zeroM extended) ->
      Exists A
        (\ x ->
          Both
            (S x)
            (Exists Nat
              (\ n ->
                Both
                  (Not (n == zero))
                  (S (iterate f n x)))))

poincare-recurrence-theorem : Set2
poincare-recurrence-theorem =
  (A R M : Set) ->
  (reals : CompleteOrderedField R) ->
  RealNumberPresentation reals ->
  (events : SigmaAlgebra A) ->
  (extended : ExtendedNonnegativeReals R M reals) ->
  ENNRealPresentation extended ->
  (measure : Measure extended events) ->
  (f : A -> A) ->
  (S : Predicate A) ->
  Conservative measure f ->
  NullMeasurableSet measure S ->
  AlmostEverywhere measure
    (\ x ->
      S x ->
      FrequentlyAtTop
        (\ n -> iterate f n x)
        S)
