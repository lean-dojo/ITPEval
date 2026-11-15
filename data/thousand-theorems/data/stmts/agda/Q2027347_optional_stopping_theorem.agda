-- Statement-only formalization of thousand-theorems corpus artifact Q2027347,
-- "Optional stopping theorem": a strongly adapted integrable real process is a
-- submartingale exactly when expected stopped values are monotone for ordered
-- bounded stopping times. This file contains no proof.

{-# OPTIONS --safe #-}

module Q2027347_optional_stopping_theorem where

open import Agda.Primitive using (Level; _⊔_)
open import Agda.Builtin.Nat using (Nat)
open import Support.Q1067156X_bounded_convergence_theorem
open import Support.Q1153584_monotone_convergence_theorem

open CompleteOrderedField
open ExtendedNonnegativeReals
open SigmaAlgebra
open Measure

record IffLevel
  {a b : Level}
  (P : Set a)
  (Q : Set b) :
  Set (a ⊔ b) where
  field
    forward :
      P -> Q
    backward :
      Q -> P

record ClassicalLogic : Set1 where
  field
    excluded-middle :
      (P : Set) ->
      Either P (Not P)

open ClassicalLogic

indicator :
  {A R : Set} ->
  (logic : ClassicalLogic) ->
  (reals : CompleteOrderedField R) ->
  Predicate A ->
  A ->
  R
indicator logic reals S x with excluded-middle logic (S x)
... | left _ =
  oneR reals
... | right _ =
  zeroR reals

setIntegral :
  {A R M : Set} ->
  {events : SigmaAlgebra A} ->
  (logic : ClassicalLogic) ->
  (reals : CompleteOrderedField R) ->
  (extended : ExtendedNonnegativeReals R M reals) ->
  ENNRealPresentation extended ->
  (measure : Measure extended events) ->
  Predicate A ->
  (A -> R) ->
  R
setIntegral logic reals extended presentation measure S f =
  realIntegral reals extended presentation measure
    (\ x ->
      multiplyR reals
        (indicator logic reals S x)
        (f x))

record Filtration
  (A : Set)
  (base : SigmaAlgebra A) : Set1 where
  field
    at :
      Nat ->
      SigmaAlgebra A

    included-in-base :
      (n : Nat) ->
      (S : Predicate A) ->
      measurable (at n) S ->
      measurable base S

    increasing :
      (i j : Nat) ->
      i <=N j ->
      (S : Predicate A) ->
      measurable (at i) S ->
      measurable (at j) S

open Filtration

record SigmaFiniteAt
  {A R M : Set}
  {reals : CompleteOrderedField R}
  {base : SigmaAlgebra A}
  {extended : ExtendedNonnegativeReals R M reals}
  (measure : Measure extended base)
  (events : SigmaAlgebra A) : Set1 where
  field
    spanning-sets :
      Nat ->
      Predicate A

    spanning-sets-measurable :
      (n : Nat) ->
      measurable events (spanning-sets n)

    spanning-sets-finite :
      (n : Nat) ->
      outerMass measure (spanning-sets n) != infinityM extended

    spanning-sets-cover :
      (x : A) ->
      Exists Nat (\ n -> spanning-sets n x)

record SigmaFiniteFiltration
  {A R M : Set}
  {reals : CompleteOrderedField R}
  {base : SigmaAlgebra A}
  {extended : ExtendedNonnegativeReals R M reals}
  (measure : Measure extended base)
  (filtration : Filtration A base) : Set1 where
  field
    sigma-finite-at :
      (n : Nat) ->
      SigmaFiniteAt measure (at filtration n)

data ExtendedNat : Set where
  finiteNat : Nat -> ExtendedNat
  infinityNat : ExtendedNat

ExtendedNatLE :
  ExtendedNat ->
  ExtendedNat ->
  Set
ExtendedNatLE (finiteNat m) (finiteNat n) =
  m <=N n
ExtendedNatLE (finiteNat m) infinityNat =
  Top
ExtendedNatLE infinityNat (finiteNat n) =
  Bottom
ExtendedNatLE infinityNat infinityNat =
  Top

StoppingTime :
  Set ->
  Set
StoppingTime A =
  A ->
  ExtendedNat

IsStoppingTime :
  {A : Set} ->
  {base : SigmaAlgebra A} ->
  Filtration A base ->
  StoppingTime A ->
  Set
IsStoppingTime filtration tau =
  (n : Nat) ->
  measurable (at filtration n)
    (\ x -> ExtendedNatLE (tau x) (finiteNat n))

StoppingTimeLE :
  {A : Set} ->
  StoppingTime A ->
  StoppingTime A ->
  Set
StoppingTimeLE {A = A} tau pi =
  (x : A) ->
  ExtendedNatLE (tau x) (pi x)

BoundedStoppingTime :
  {A : Set} ->
  StoppingTime A ->
  Set
BoundedStoppingTime {A = A} tau =
  Exists Nat
    (\ bound ->
      (x : A) ->
      ExtendedNatLE (tau x) (finiteNat bound))

stoppedValue :
  {A R : Set} ->
  CompleteOrderedField R ->
  (Nat -> A -> R) ->
  StoppingTime A ->
  A ->
  R
stoppedValue reals process tau x with tau x
... | finiteNat n =
  process n x
... | infinityNat =
  zeroR reals

ExpectedStoppedValue :
  {A R M : Set} ->
  {base : SigmaAlgebra A} ->
  (reals : CompleteOrderedField R) ->
  (extended : ExtendedNonnegativeReals R M reals) ->
  ENNRealPresentation extended ->
  (measure : Measure extended base) ->
  (Nat -> A -> R) ->
  StoppingTime A ->
  R
ExpectedStoppedValue reals extended presentation measure process tau =
  realIntegral reals extended presentation measure
    (stoppedValue reals process tau)

StronglyAdapted :
  {A R : Set} ->
  {base : SigmaAlgebra A} ->
  (reals : CompleteOrderedField R) ->
  Filtration A base ->
  (Nat -> A -> R) ->
  Set
StronglyAdapted reals filtration process =
  (n : Nat) ->
  MeasurableOrder
    (at filtration n)
    (lessOrEqualR reals)
    (process n)

record Submartingale
  {A R M : Set}
  {base : SigmaAlgebra A}
  {reals : CompleteOrderedField R}
  {extended : ExtendedNonnegativeReals R M reals}
  (logic : ClassicalLogic)
  (presentation : ENNRealPresentation extended)
  (measure : Measure extended base)
  (filtration : Filtration A base)
  (process : Nat -> A -> R) : Set1 where
  field
    strongly-adapted :
      StronglyAdapted reals filtration process

    integrable-values :
      (n : Nat) ->
      RealIntegrable reals base extended measure (process n)

    set-integral-monotone :
      (i j : Nat) ->
      i <=N j ->
      (S : Predicate A) ->
      measurable (at filtration i) S ->
      lessOrEqualR reals
        (setIntegral logic reals extended presentation measure S (process i))
        (setIntegral logic reals extended presentation measure S (process j))

optional-stopping-theorem : Set2
optional-stopping-theorem =
  (A R M : Set) ->
  (reals : CompleteOrderedField R) ->
  RealNumberPresentation reals ->
  (base : SigmaAlgebra A) ->
  (extended : ExtendedNonnegativeReals R M reals) ->
  (presentation : ENNRealPresentation extended) ->
  (measure : Measure extended base) ->
  (filtration : Filtration A base) ->
  SigmaFiniteFiltration measure filtration ->
  (logic : ClassicalLogic) ->
  (process : Nat -> A -> R) ->
  StronglyAdapted reals filtration process ->
  ((n : Nat) ->
    RealIntegrable reals base extended measure (process n)) ->
  IffLevel
    (Submartingale logic presentation measure filtration process)
    ((tau pi : StoppingTime A) ->
      IsStoppingTime filtration tau ->
      IsStoppingTime filtration pi ->
      StoppingTimeLE tau pi ->
      BoundedStoppingTime pi ->
      lessOrEqualR reals
        (ExpectedStoppedValue
          reals extended presentation measure process tau)
        (ExpectedStoppedValue
          reals extended presentation measure process pi))
