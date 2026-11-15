-- Statement-only formalization of thousand-theorems corpus artifact Q834025,
-- "Cauchy integral theorem": the Cauchy integral formula for a complex-valued
-- function continuous on a closed disc and complex differentiable in its
-- interior outside a countable set. This file contains no proof.

{-# OPTIONS --safe #-}

module Q834025_cauchy_integral_theorem where

open import Agda.Builtin.Equality renaming (_≡_ to _==_)
open import Agda.Builtin.Nat using (zero; suc)
open import Support.CauchyIntegral

open CompleteOrderedField
open CanonicalComplexTranscendentals

cauchy-integral-theorem : Set2
cauchy-integral-theorem =
  (R : Set) ->
  (reals : CompleteOrderedField R) ->
  RealNumberPresentation reals ->
  (complexNorm : ComplexNorm reals) ->
  (transcendentals :
    CanonicalComplexTranscendentals reals complexNorm) ->
  (radius : R) ->
  (center point : Complex R) ->
  (exceptional : SetOf (Complex R)) ->
  CountableComplexSet exceptional ->
  OpenBall reals complexNorm center radius point ->
  (f : Complex R -> Complex R) ->
  ContinuousOn reals complexNorm f
    (ClosedBall reals complexNorm center radius) ->
  ((z : Complex R) ->
    OpenBall reals complexNorm center radius z ->
    Not (exceptional z) ->
    ComplexDifferentiableAt reals complexNorm f z) ->
  RiemannIntegralOn reals complexNorm
    (zeroR reals)
    (multiplyR reals
      (fromNatR reals (suc (suc zero)))
      (piR transcendentals))
    (\ theta ->
      circleIntegrand reals transcendentals
        center radius point f theta)
    (twoPiITimes reals transcendentals (f point))
