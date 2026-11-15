-- Statement-only formalization of thousand-theorems corpus artifact Q1443036,
-- "Parseval's theorem": for every complex L2 function on a positive-period
-- additive circle, the sum over all integer Fourier modes of the squared
-- coefficient norms equals the integral of the squared function norm.
-- This file contains no proof.

{-# OPTIONS --safe #-}

module Q1443036_parseval_s_theorem where

open import Support.Bochner
open import Support.Fourier
open import Agda.Builtin.Equality renaming (_≡_ to _==_)
open import Agda.Builtin.Nat using (Nat; zero; suc)

open CompleteOrderedField
open NormedVectorSpace
open ComplexNumber
open ComplexModulus
open ComplexNormedSpace
open SigmaAlgebra
open ExtendedNonnegativeReals
open Measure
open BochnerIntegration

data Integer : Set where
  nonnegative      : Nat -> Integer
  negativeSuccessor : Nat -> Integer

negateInteger :
  Integer ->
  Integer
negateInteger (nonnegative zero) =
  nonnegative zero
negateInteger (nonnegative (suc n)) =
  negativeSuccessor n
negateInteger (negativeSuccessor n) =
  nonnegative (suc n)

integerToReal :
  {R : Set} ->
  CompleteOrderedField R ->
  Integer ->
  R
integerToReal reals (nonnegative n) =
  fromNatR reals n
integerToReal reals (negativeSuccessor n) =
  negateR reals (fromNatR reals (suc n))

integerScale :
  {R : Set} ->
  CompleteOrderedField R ->
  Integer ->
  R ->
  R
integerScale reals n x =
  multiplyR reals (integerToReal reals n) x

fourierPhase :
  {R : Set} ->
  CompleteOrderedField R ->
  R ->
  R ->
  Integer ->
  R ->
  ComplexNumber R
fourierPhase reals pi period n x =
  complex
    (zeroR reals)
    (multiplyR reals
      (multiplyR reals
        (multiplyR reals
          (fromNatR reals (suc (suc zero)))
          pi)
        (integerToReal reals n))
      (multiplyR reals x (reciprocalR reals period)))

record FiniteSelection (A : Set) : Set where
  field
    size :
      Nat
    entry :
      Fin size -> A
    entry-injective :
      (i j : Fin size) ->
      entry i == entry j ->
      i == j

open FiniteSelection

finiteSubsum :
  {A R : Set} ->
  CompleteOrderedField R ->
  (A -> R) ->
  FiniteSelection A ->
  R
finiteSubsum reals terms selection =
  sumVector reals (size selection)
    (\ i -> terms (entry selection i))

IndexedSumEquals :
  {A R : Set} ->
  CompleteOrderedField R ->
  (A -> R) ->
  R ->
  Set
IndexedSumEquals {A = A} {R = R} reals terms value =
  Both
    ((selection : FiniteSelection A) ->
      lessOrEqualR reals
        (finiteSubsum reals terms selection)
        value)
    ((upper : R) ->
      ((selection : FiniteSelection A) ->
        lessOrEqualR reals
          (finiteSubsum reals terms selection)
          upper) ->
      lessOrEqualR reals value upper)

CircleOpen :
  {R Circle : Set} ->
  CompleteOrderedField R ->
  (R -> Circle) ->
  Predicate Circle ->
  Set
CircleOpen {R = R} reals lift U =
  (x : R) ->
  U (lift x) ->
  Exists R
    (\ radius ->
      Both
        (Positive reals radius)
        ((y : R) ->
          StrictLess reals (distanceR reals y x) radius ->
          U (lift y)))

data CircleBorelGenerated
  {R Circle : Set}
  (reals : CompleteOrderedField R)
  (lift : R -> Circle) :
  Predicate Circle -> Set1 where
  circle-borel-open :
    {U : Predicate Circle} ->
    CircleOpen reals lift U ->
    CircleBorelGenerated reals lift U
  circle-borel-empty :
    CircleBorelGenerated reals lift emptySet
  circle-borel-complement :
    {S : Predicate Circle} ->
    CircleBorelGenerated reals lift S ->
    CircleBorelGenerated reals lift (complement S)
  circle-borel-countable-union :
    (sets : Nat -> Predicate Circle) ->
    ((n : Nat) -> CircleBorelGenerated reals lift (sets n)) ->
    CircleBorelGenerated reals lift (countableUnion sets)
  circle-borel-congruent :
    {S T : Predicate Circle} ->
    ((x : Circle) -> Iff (S x) (T x)) ->
    CircleBorelGenerated reals lift S ->
    CircleBorelGenerated reals lift T

translatedSet :
  {Circle : Set} ->
  (Circle -> Circle -> Circle) ->
  Circle ->
  Predicate Circle ->
  Predicate Circle
translatedSet addCircle shift S x =
  S (addCircle shift x)

record ParsevalContext
  (R M Circle : Set) : Set2 where
  field
    reals :
      CompleteOrderedField R
    real-number-presentation :
      RealNumberPresentation reals
    complex-modulus :
      ComplexModulus reals

    scalar-space :
      ComplexNormedSpace R (ComplexNumber R) reals complex-modulus
    scalar-zero :
      zeroE (realSpace scalar-space) ==
      zeroC reals
    scalar-add :
      (x y : ComplexNumber R) ->
      addE (realSpace scalar-space) x y ==
      addC reals x y
    scalar-negate :
      (x : ComplexNumber R) ->
      negateE (realSpace scalar-space) x ==
      negateC reals x
    scalar-real-scale :
      (a : R) ->
      (z : ComplexNumber R) ->
      scaleE (realSpace scalar-space) a z ==
      multiplyC reals (fromReal reals a) z
    scalar-complex-scale :
      (a z : ComplexNumber R) ->
      scaleC scalar-space a z ==
      multiplyC reals a z
    scalar-norm :
      (z : ComplexNumber R) ->
      normE (realSpace scalar-space) z ==
      modulus complex-modulus z
    scalar-complete :
      Complete reals
        (distanceE (realSpace scalar-space))

    period :
      R
    period-positive :
      Positive reals period

    lift :
      R -> Circle
    lift-surjective :
      (point : Circle) ->
      Exists R (\ x -> lift x == point)
    lift-equality :
      (x y : R) ->
      Iff
        (lift x == lift y)
        (Exists Integer
          (\ n ->
            subtractR reals x y ==
            integerScale reals n period))

    circle-zero :
      Circle
    circle-add :
      Circle -> Circle -> Circle
    lift-zero :
      lift (zeroR reals) == circle-zero
    lift-add :
      (x y : R) ->
      lift (addR reals x y) ==
      circle-add (lift x) (lift y)

    pi :
      R
    pi-value :
      PiValue reals pi
    exponential :
      ComplexNumber R -> ComplexNumber R
    exponential-value :
      (z : ComplexNumber R) ->
      ComplexExponentialValue reals complex-modulus z (exponential z)

    character :
      Integer -> Circle -> ComplexNumber R
    character-on-lifts :
      (n : Integer) ->
      (x : R) ->
      character n (lift x) ==
      exponential (fourierPhase reals pi period n x)

    events :
      SigmaAlgebra Circle
    borel-measurable :
      (S : Predicate Circle) ->
      CircleBorelGenerated reals lift S ->
      measurable events S
    measurable-borel :
      (S : Predicate Circle) ->
      measurable events S ->
      CircleBorelGenerated reals lift S

    extended :
      ExtendedNonnegativeReals R M reals
    haar :
      Measure extended events
    haar-total-mass :
      outerMass haar wholeSet ==
      finiteM extended
        (oneR reals)
        (Both.first (zero-less-than-one reals))
    haar-translation-invariant :
      (shift : Circle) ->
      (S : Predicate Circle) ->
      outerMass haar (translatedSet circle-add shift S) ==
      outerMass haar S

    integration :
      BochnerIntegration reals
        (realSpace scalar-space)
        events
        extended
        haar

open ParsevalContext

squaredModulus :
  {R M Circle : Set} ->
  (context : ParsevalContext R M Circle) ->
  ComplexNumber R ->
  R
squaredModulus context z =
  multiplyR (reals context)
    (modulus (complex-modulus context) z)
    (modulus (complex-modulus context) z)

record L2Function
  {R M Circle : Set}
  (context : ParsevalContext R M Circle) : Set1 where
  field
    representative :
      Circle -> ComplexNumber R
    strongly-measurable :
      AEStronglyMeasurable
        (reals context)
        (events context)
        (haar context)
        (distanceE (realSpace (scalar-space context)))
        representative
    square-integral-definition :
      LowerIntegralValue
        (extended context)
        (events context)
        (haar context)
        (\ point -> squaredModulus context (representative point))
        (lowerIntegral (integration context)
          (\ point -> squaredModulus context (representative point)))
    square-integral-finite :
      lowerIntegral (integration context)
        (\ point -> squaredModulus context (representative point)) !=
      infinityM (extended context)

open L2Function

fourierCoefficient :
  {R M Circle : Set} ->
  (context : ParsevalContext R M Circle) ->
  L2Function context ->
  Integer ->
  ComplexNumber R
fourierCoefficient context f n =
  integralVector (integration context)
    (\ point ->
      multiplyC (reals context)
        (character context (negateInteger n) point)
        (representative f point))

squareIntegral :
  {R M Circle : Set} ->
  (context : ParsevalContext R M Circle) ->
  L2Function context ->
  R
squareIntegral context f =
  realPart
    (integralVector (integration context)
      (\ point ->
        fromReal (reals context)
          (squaredModulus context (representative f point))))

parseval-theorem : Set2
parseval-theorem =
  (R M Circle : Set) ->
  (context : ParsevalContext R M Circle) ->
  (f : L2Function context) ->
  IndexedSumEquals
    (reals context)
    (\ n -> squaredModulus context (fourierCoefficient context f n))
    (squareIntegral context f)
