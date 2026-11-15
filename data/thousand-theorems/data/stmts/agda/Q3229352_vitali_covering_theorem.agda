-- Statement-only formalization of thousand-theorems corpus artifact Q3229352,
-- "Vitali covering theorem": a fine family of closed sets satisfying a
-- uniform measure-growth bound has a countable pairwise-disjoint subfamily
-- covering the given set almost everywhere. This file contains no proof.

{-# OPTIONS --safe #-}

module Q3229352_vitali_covering_theorem where

open import Agda.Builtin.Equality renaming (_≡_ to _==_)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Support.Q1067156X_bounded_convergence_theorem
open import Support.Q2275191_lebesgue_differentiation_theorem

open CompleteOrderedField
open SigmaAlgebra
open ExtendedNonnegativeReals
open Measure

OpensMeasurableMetric :
  {A R : Set} ->
  {reals : CompleteOrderedField R} ->
  PseudoMetricSpace R A reals ->
  SigmaAlgebra A ->
  Set1
OpensMeasurableMetric metric events =
  (U : Predicate _) ->
  MetricOpen metric U ->
  measurable events U

IsClosedMetric :
  {A R : Set} ->
  {reals : CompleteOrderedField R} ->
  PseudoMetricSpace R A reals ->
  Predicate A ->
  Set
IsClosedMetric metric S =
  MetricOpen metric (complement S)

record ElementOf
  {I : Set}
  (S : Predicate I) : Set where
  constructor member
  field
    element    : I
    membership : S element

open ElementOf

record CountableSubset
  {I : Set}
  (S : Predicate I) : Set where
  field
    code :
      ElementOf S -> Nat
    code-injective :
      (x y : ElementOf S) ->
      code x == code y ->
      element x == element y

SubfamilyUnion :
  {A I : Set} ->
  Predicate I ->
  (I -> Predicate A) ->
  Predicate A
SubfamilyUnion {I = I} indices family x =
  Exists I
    (\ i ->
      Both
        (indices i)
        (family i x))

SetPairwiseDisjoint :
  {A I : Set} ->
  Predicate I ->
  (I -> Predicate A) ->
  Set
SetPairwiseDisjoint {A = A} {I = I} indices family =
  (i j : I) ->
  indices i ->
  indices j ->
  i != j ->
  (x : A) ->
  family i x ->
  family j x ->
  Bottom

threeR :
  {R : Set} ->
  CompleteOrderedField R ->
  R
threeR reals =
  fromNatR reals (suc (suc (suc zero)))

record VitaliCoveringConclusion
  {A I R M : Set}
  {reals : CompleteOrderedField R}
  {events : SigmaAlgebra A}
  {extended : ExtendedNonnegativeReals R M reals}
  (measure : Measure extended events)
  (S : Predicate A)
  (familyIndices : Predicate I)
  (family : I -> Predicate A) : Set1 where
  field
    selected :
      Predicate I
    selected-in-family :
      Subset selected familyIndices
    selected-countable :
      CountableSubset selected
    selected-pairwise-disjoint :
      SetPairwiseDisjoint selected family
    covers-almost-everywhere :
      outerMass measure
        (SetDifference S (SubfamilyUnion selected family))
      ==
      zeroM extended

vitali-covering-theorem : Set2
vitali-covering-theorem =
  (A I R M : Set) ->
  (reals : CompleteOrderedField R) ->
  RealNumberPresentation reals ->
  (metric : PseudoMetricSpace R A reals) ->
  SecondCountableMetric metric ->
  (events : SigmaAlgebra A) ->
  OpensMeasurableMetric metric events ->
  (extended : ExtendedNonnegativeReals R M reals) ->
  ENNRealPresentation extended ->
  (measure : Measure extended events) ->
  IsLocallyFiniteMeasure metric measure ->
  (S : Predicate A) ->
  (familyIndices : Predicate I) ->
  (constant : NonnegativeReal reals) ->
  (radius : I -> R) ->
  (center : I -> A) ->
  (family : I -> Predicate A) ->
  ((i : I) ->
    familyIndices i ->
    Subset
      (family i)
      (ClosedBall metric (center i) (radius i))) ->
  ((i : I) ->
    familyIndices i ->
    lessOrEqualM extended
      (outerMass measure
        (ClosedBall metric (center i)
          (multiplyR reals (threeR reals) (radius i))))
      (multiplyM extended
        (finiteNN extended constant)
        (outerMass measure (family i)))) ->
  ((i : I) ->
    familyIndices i ->
    InteriorNonempty metric (family i)) ->
  ((i : I) ->
    familyIndices i ->
    IsClosedMetric metric (family i)) ->
  ((x : A) ->
    S x ->
    (epsilon : R) ->
    Positive reals epsilon ->
    Exists I
      (\ i ->
        Both
          (familyIndices i)
          (Both
            (lessOrEqualR reals (radius i) epsilon)
            (center i == x)))) ->
  VitaliCoveringConclusion measure S familyIndices family
