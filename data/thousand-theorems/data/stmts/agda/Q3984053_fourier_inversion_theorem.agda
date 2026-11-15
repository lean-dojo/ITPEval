-- Statement-only formalization of thousand-theorems corpus artifact Q3984053,
-- "Fourier inversion theorem": a continuous integrable function from a
-- finite-dimensional real inner-product space to a complete complex normed
-- space is recovered by inverse Fourier transformation when its Fourier
-- transform is integrable. This file contains no proof.

{-# OPTIONS --safe #-}

module Q3984053_fourier_inversion_theorem where

open import Support.Fourier

open ComplexNormedSpace
open FourierContext

fourier-inversion-theorem : Set2
fourier-inversion-theorem =
  (R M V E : Set) ->
  (context : FourierContext R M V E) ->
  (f : V -> E) ->
  Continuous
    (reals context)
    (domain context)
    (realSpace (codomain context))
    f ->
  IntegrableInContext context f ->
  IntegrableInContext context (fourierInContext context f) ->
  FunctionEqual
    (inverseFourierInContext context
      (fourierInContext context f))
    f
