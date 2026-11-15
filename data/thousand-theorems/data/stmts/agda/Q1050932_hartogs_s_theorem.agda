-- Statement-only formalization of thousand-theorems corpus artifact Q1050932,
-- "Hartogs's theorem": a function from two complex variables to a
-- second-countable complex Banach space that is analytic separately in each
-- variable on an open set is jointly analytic there. This file contains no proof.

{-# OPTIONS --safe #-}

module Q1050932_hartogs_s_theorem where

open import Support.Hartogs
open import Support.Liouville

hartogs-theorem : Set2
hartogs-theorem =
  (R E : Set) ->
  (reals : CompleteOrderedField R) ->
  RealNumberPresentation reals ->
  (complexNorm : ComplexNorm reals) ->
  (complexSpace :
    NormedComplexVectorSpace reals complexNorm (Complex R)) ->
  ComplexSpacePresentation reals complexNorm complexSpace ->
  (pairSpace :
    NormedComplexVectorSpace reals complexNorm
      (Pair (Complex R) (Complex R))) ->
  PairSpacePresentation
    reals complexNorm complexSpace pairSpace ->
  (target :
    NormedComplexVectorSpace reals complexNorm E) ->
  CompleteMetric reals target ->
  SecondCountableMetric reals target ->
  (function : Pair (Complex R) (Complex R) -> E) ->
  (U : SetOf (Pair (Complex R) (Complex R))) ->
  OpenInNormedSpace reals pairSpace U ->
  ((c0 c1 : Complex R) ->
    U (pair c0 c1) ->
    AnalyticAt
      reals complexNorm complexSpace target
      (\ z0 -> function (pair z0 c1))
      c0) ->
  ((c0 c1 : Complex R) ->
    U (pair c0 c1) ->
    AnalyticAt
      reals complexNorm complexSpace target
      (\ z1 -> function (pair c0 z1))
      c1) ->
  AnalyticOnNeighborhood
    reals complexNorm pairSpace target function U
