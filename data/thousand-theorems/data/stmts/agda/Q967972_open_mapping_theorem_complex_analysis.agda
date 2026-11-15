-- Statement-only formalization of thousand-theorems corpus artifact Q967972
-- (thousand-theorems__agda__Q967972), "Open mapping theorem (complex
-- analysis)": a complex-valued function analytic on a preconnected subset of
-- a complex normed space is constant there or maps every open subset contained
-- in it to an open subset of the complex plane. This file contains no proof.

{-# OPTIONS --safe #-}

module Q967972OpenMappingTheoremComplexAnalysis where

open import Agda.Builtin.Equality renaming (_≡_ to _==_)
open import Support.OpenMapping

open-mapping-theorem-complex-analysis : Set2
open-mapping-theorem-complex-analysis =
  (R E : Set) ->
  (reals : CompleteOrderedField R) ->
  RealNumberPresentation reals ->
  (complexNorm : ComplexNorm reals) ->
  (complexSpace :
    NormedComplexVectorSpace reals complexNorm (Complex R)) ->
  ComplexSpacePresentation reals complexNorm complexSpace ->
  (source : NormedComplexVectorSpace reals complexNorm E) ->
  (U : SetOf E) ->
  (function : E -> Complex R) ->
  AnalyticOnNeighborhood
    reals complexNorm source complexSpace function U ->
  Preconnected reals source U ->
  MixedEither
    (Exists (Complex R)
      (\ value ->
        (z : E) ->
        U z ->
        function z == value))
    ((S : SetOf E) ->
      Subset S U ->
      OpenInNormedSpace reals source S ->
      OpenInNormedSpace reals complexSpace (Image function S))
