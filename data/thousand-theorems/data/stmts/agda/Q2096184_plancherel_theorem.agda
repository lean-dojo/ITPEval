-- Statement-only formalization of thousand-theorems corpus artifact Q2096184,
-- "Plancherel theorem": the Fourier transform preserves the integral of the
-- pointwise complex inner product of Hilbert-valued Schwartz functions on a
-- finite-dimensional real inner-product space. This file contains no proof.

{-# OPTIONS --safe #-}

module Q2096184_plancherel_theorem where

open import Support.Bochner
open import Support.Fourier
open import Agda.Builtin.Equality renaming (_≡_ to _==_)
open import Agda.Builtin.Nat using (Nat; zero; suc)

open CompleteOrderedField
open NormedVectorSpace
open ComplexNumber
open ComplexModulus
open ComplexNormedSpace
open FourierContext
open EuclideanLebesguePresentation
open BochnerIntegration

conjugateC :
  {R : Set} ->
  CompleteOrderedField R ->
  ComplexNumber R ->
  ComplexNumber R
conjugateC reals z =
  complex (realPart z) (negateR reals (imaginaryPart z))

emptyVector :
  {A : Set} ->
  Vector A zero
emptyVector ()

prependVector :
  {A : Set} ->
  {n : Nat} ->
  A ->
  Vector A n ->
  Vector A (suc n)
prependVector x xs fzero =
  x
prependVector x xs (fsuc i) =
  xs i

record ComplexHilbertStructure
  {R M V H : Set}
  (context : FourierContext R M V H) : Set1 where
  field
    innerH :
      H -> H -> ComplexNumber R

    inner-add-left :
      (x y z : H) ->
      innerH
        (addE (realSpace (codomain context)) x y)
        z ==
      addC (reals context) (innerH x z) (innerH y z)

    inner-scale-left :
      (a : ComplexNumber R) ->
      (x y : H) ->
      innerH (scaleC (codomain context) a x) y ==
      multiplyC (reals context)
        (conjugateC (reals context) a)
        (innerH x y)

    inner-add-right :
      (x y z : H) ->
      innerH x
        (addE (realSpace (codomain context)) y z) ==
      addC (reals context) (innerH x y) (innerH x z)

    inner-scale-right :
      (a : ComplexNumber R) ->
      (x y : H) ->
      innerH x (scaleC (codomain context) a y) ==
      multiplyC (reals context) a (innerH x y)

    inner-conjugate-symmetry :
      (x y : H) ->
      innerH x y ==
      conjugateC (reals context) (innerH y x)

    inner-nonnegative :
      (x : H) ->
      lessOrEqualR (reals context)
        (zeroR (reals context))
        (realPart (innerH x x))

    inner-definite :
      (x : H) ->
      innerH x x == zeroC (reals context) ->
      x == zeroE (realSpace (codomain context))

    inner-norm-square :
      (x : H) ->
      realPart (innerH x x) ==
      multiplyR (reals context)
        (normE (realSpace (codomain context)) x)
        (normE (realSpace (codomain context)) x)

open ComplexHilbertStructure

DirectionalDerivative :
  {R M V H : Set} ->
  (context : FourierContext R M V H) ->
  (V -> H) ->
  V ->
  V ->
  H ->
  Set
DirectionalDerivative {R = R} context f point direction derivative =
  (epsilon : R) ->
  Positive (reals context) epsilon ->
  Exists R
    (\ delta ->
      Both
        (Positive (reals context) delta)
        ((t : R) ->
          Positive (reals context) (absoluteR (reals context) t) ->
          StrictLess (reals context)
            (absoluteR (reals context) t)
            delta ->
          StrictLess (reals context)
            (distanceE (realSpace (codomain context))
              (scaleE (realSpace (codomain context))
                (reciprocalR (reals context) t)
                (subtractE (realSpace (codomain context))
                  (f
                    (addE (domain context) point
                      (scaleE (domain context) t direction)))
                  (f point)))
              derivative)
            epsilon))

UnitDirections :
  {R M V H : Set} ->
  (context : FourierContext R M V H) ->
  {n : Nat} ->
  Vector V n ->
  Set
UnitDirections context {n = n} directions =
  (i : Fin n) ->
  lessOrEqualR (reals context)
    (normE (domain context) (directions i))
    (oneR (reals context))

record SchwartzMap
  {R M V H : Set}
  (context : FourierContext R M V H) : Set1 where
  field
    function :
      V -> H

    derivatives :
      (n : Nat) ->
      V ->
      Vector V n ->
      H

    derivative-zero :
      (x : V) ->
      derivatives zero x emptyVector == function x

    derivative-successor :
      (n : Nat) ->
      (directions : Vector V n) ->
      (x direction : V) ->
      DirectionalDerivative context
        (\ y -> derivatives n y directions)
        x
        direction
        (derivatives (suc n) x
          (prependVector direction directions))

    derivatives-continuous :
      (n : Nat) ->
      (directions : Vector V n) ->
      Continuous
        (reals context)
        (domain context)
        (realSpace (codomain context))
        (\ x -> derivatives n x directions)

    rapidly-decreasing :
      (n weight : Nat) ->
      Exists R
        (\ bound ->
          Both
            (lessOrEqualR (reals context)
              (zeroR (reals context))
              bound)
            ((x : V) ->
              (directions : Vector V n) ->
              UnitDirections context directions ->
              lessOrEqualR (reals context)
                (multiplyR (reals context)
                  (powerR (reals context)
                    (addR (reals context)
                      (oneR (reals context))
                      (normE (domain context) x))
                    weight)
                  (normE (realSpace (codomain context))
                    (derivatives n x directions)))
                bound))

open SchwartzMap

record PlancherelContext
  (R M V H : Set) : Set2 where
  field
    fourier-context :
      FourierContext R M V H

    hilbert-space :
      ComplexHilbertStructure fourier-context

    scalar-space :
      ComplexNormedSpace R (ComplexNumber R)
        (reals fourier-context)
        (complex-modulus fourier-context)

    scalar-zero :
      zeroE (realSpace scalar-space) ==
      zeroC (reals fourier-context)

    scalar-add :
      (x y : ComplexNumber R) ->
      addE (realSpace scalar-space) x y ==
      addC (reals fourier-context) x y

    scalar-negate :
      (x : ComplexNumber R) ->
      negateE (realSpace scalar-space) x ==
      negateC (reals fourier-context) x

    scalar-real-scale :
      (a : R) ->
      (z : ComplexNumber R) ->
      scaleE (realSpace scalar-space) a z ==
      multiplyC (reals fourier-context)
        (fromReal (reals fourier-context) a)
        z

    scalar-complex-scale :
      (a z : ComplexNumber R) ->
      scaleC scalar-space a z ==
      multiplyC (reals fourier-context) a z

    scalar-norm :
      (z : ComplexNumber R) ->
      normE (realSpace scalar-space) z ==
      modulus (complex-modulus fourier-context) z

    scalar-complete :
      Complete
        (reals fourier-context)
        (distanceE (realSpace scalar-space))

    scalar-integration :
      BochnerIntegration
        (reals fourier-context)
        (realSpace scalar-space)
        (events (lebesgue fourier-context))
        (extended (lebesgue fourier-context))
        (volume (lebesgue fourier-context))

open PlancherelContext

scalarIntegral :
  {R M V H : Set} ->
  (context : PlancherelContext R M V H) ->
  (V -> ComplexNumber R) ->
  ComplexNumber R
scalarIntegral context =
  integralVector (scalar-integration context)

plancherel-theorem : Set2
plancherel-theorem =
  (R M V H : Set) ->
  (context : PlancherelContext R M V H) ->
  (f g : SchwartzMap (fourier-context context)) ->
  scalarIntegral context
    (\ frequency ->
      innerH (hilbert-space context)
        (fourierInContext (fourier-context context)
          (function f)
          frequency)
        (fourierInContext (fourier-context context)
          (function g)
          frequency)) ==
  scalarIntegral context
    (\ point ->
      innerH (hilbert-space context)
        (function f point)
        (function g point))
