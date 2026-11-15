-- Statement-only formalization of thousand-theorems corpus artifact Q6813106,
-- "Mellin inversion theorem": for a function into a complete complex normed
-- space, Mellin convergence at a real parameter, vertical integrability of
-- its Mellin transform along that line, positivity of the input, and
-- continuity there imply that inverse Mellin transformation recovers the
-- function value. This file contains no proof.

{-# OPTIONS --safe #-}

module Q6813106_mellin_inversion_theorem where

open import Support.Bochner
open import Support.Mellin
open import Agda.Builtin.Equality renaming (_≡_ to _==_)

open CompleteOrderedField
open ComplexNormedSpace
open MellinContext

mellin-inversion : Set2
mellin-inversion =
  (R M E : Set) ->
  (context : MellinContext R M E) ->
  (sigma : R) ->
  (f : R -> E) ->
  (x : R) ->
  Positive (reals context) x ->
  MellinConvergent context f
    (fromReal (reals context) sigma) ->
  VerticalIntegrable context (mellin context f) sigma ->
  ContinuousAt context f x ->
  mellinInv context sigma (mellin context f) x == f x
