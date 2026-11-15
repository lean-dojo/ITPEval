-- Statement-only formalization of thousand-theorems corpus artifact Q5445112,
-- "Fernique's theorem": every Gaussian measure on a complete second-countable
-- real normed space exponentially integrates a positive multiple of the
-- squared norm. This file contains no proof.

{-# OPTIONS --safe #-}

module Q5445112_fernique_s_theorem where

open import Agda.Builtin.Equality renaming (_≡_ to _==_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)
open import Support.Q1067156X_bounded_convergence_theorem

open CompleteOrderedField
open NormedVectorSpace
open ExtendedNonnegativeReals
open SigmaAlgebra
open Measure

record BothLarge (A : Set) (B : Set1) : Set1 where
  constructor both-large
  field
    small-part : A
    large-part : B

record ExistsLarge (A : Set) (P : A -> Set1) : Set1 where
  constructor witness-large
  field
    large-value    : A
    large-property : P large-value

Nonnegative :
  {R : Set} ->
  CompleteOrderedField R ->
  R ->
  Set
Nonnegative reals x =
  lessOrEqualR reals (zeroR reals) x

divideR :
  {R : Set} ->
  CompleteOrderedField R ->
  R ->
  R ->
  R
divideR reals x y =
  multiplyR reals x (reciprocalR reals y)

squareR :
  {R : Set} ->
  CompleteOrderedField R ->
  R ->
  R
squareR reals x =
  multiplyR reals x x

powerR :
  {R : Set} ->
  CompleteOrderedField R ->
  R ->
  Nat ->
  R
powerR reals x zero =
  oneR reals
powerR reals x (suc n) =
  multiplyR reals (powerR reals x n) x

factorial : Nat -> Nat
factorial zero =
  suc zero
factorial (suc n) =
  suc n * factorial n

alternatingSign :
  {R : Set} ->
  CompleteOrderedField R ->
  Nat ->
  R
alternatingSign reals zero =
  oneR reals
alternatingSign reals (suc n) =
  negateR reals (alternatingSign reals n)

evenIndex : Nat -> Nat
evenIndex n =
  n + n

oddIndex : Nat -> Nat
oddIndex n =
  suc (evenIndex n)

sumFirstR :
  {R : Set} ->
  CompleteOrderedField R ->
  (Nat -> R) ->
  Nat ->
  R
sumFirstR reals terms zero =
  zeroR reals
sumFirstR reals terms (suc n) =
  addR reals (sumFirstR reals terms n) (terms n)

exponentialPartialSum :
  {R : Set} ->
  CompleteOrderedField R ->
  R ->
  Nat ->
  R
exponentialPartialSum reals x n =
  sumFirstR reals
    (\ k ->
      divideR reals
        (powerR reals x k)
        (fromNatR reals (factorial k)))
    n

cosinePartialSum :
  {R : Set} ->
  CompleteOrderedField R ->
  R ->
  Nat ->
  R
cosinePartialSum reals x n =
  sumFirstR reals
    (\ k ->
      multiplyR reals
        (alternatingSign reals k)
        (divideR reals
          (powerR reals x (evenIndex k))
          (fromNatR reals (factorial (evenIndex k)))))
    n

sinePartialSum :
  {R : Set} ->
  CompleteOrderedField R ->
  R ->
  Nat ->
  R
sinePartialSum reals x n =
  sumFirstR reals
    (\ k ->
      multiplyR reals
        (alternatingSign reals k)
        (divideR reals
          (powerR reals x (oddIndex k))
          (fromNatR reals (factorial (oddIndex k)))))
    n

record RealTranscendentalFunctions
  {R : Set}
  (reals : CompleteOrderedField R) : Set1 where
  field
    exponential cosine sine :
      R -> R
    exponential-series :
      (x : R) ->
      SequentialLimit reals (distanceR reals)
        (exponentialPartialSum reals x)
        (exponential x)
    cosine-series :
      (x : R) ->
      SequentialLimit reals (distanceR reals)
        (cosinePartialSum reals x)
        (cosine x)
    sine-series :
      (x : R) ->
      SequentialLimit reals (distanceR reals)
        (sinePartialSum reals x)
        (sine x)

open RealTranscendentalFunctions

MetricOpen :
  {R A : Set} ->
  CompleteOrderedField R ->
  (A -> A -> R) ->
  Predicate A ->
  Set
MetricOpen {R = R} {A = A} reals distance U =
  (x : A) ->
  U x ->
  Exists R
    (\ radius ->
      Both
        (Positive reals radius)
        ((y : A) ->
          StrictLess reals (distance y x) radius ->
          U y))

record SecondCountableMetric
  {R A : Set}
  (reals : CompleteOrderedField R)
  (distance : A -> A -> R) : Set2 where
  field
    countable-basis :
      Nat -> Predicate A
    basis-open :
      (n : Nat) ->
      MetricOpen reals distance (countable-basis n)
    basis-refines :
      (U : Predicate A) ->
      MetricOpen reals distance U ->
      (x : A) ->
      U x ->
      Exists Nat
        (\ n ->
          Both
            (countable-basis n x)
            (Subset (countable-basis n) U))

data BorelGenerated
  {R A : Set}
  (reals : CompleteOrderedField R)
  (distance : A -> A -> R) :
  Predicate A -> Set1 where

  borel-open :
    {U : Predicate A} ->
    MetricOpen reals distance U ->
    BorelGenerated reals distance U

  borel-empty :
    BorelGenerated reals distance emptySet

  borel-complement :
    {S : Predicate A} ->
    BorelGenerated reals distance S ->
    BorelGenerated reals distance (complement S)

  borel-countable-union :
    (sets : Nat -> Predicate A) ->
    ((n : Nat) -> BorelGenerated reals distance (sets n)) ->
    BorelGenerated reals distance (countableUnion sets)

  borel-congruent :
    {S T : Predicate A} ->
    ((x : A) -> Iff (S x) (T x)) ->
    BorelGenerated reals distance S ->
    BorelGenerated reals distance T

record BorelSpace
  {R A : Set}
  (reals : CompleteOrderedField R)
  (distance : A -> A -> R)
  (events : SigmaAlgebra A) : Set2 where
  field
    borel-measurable :
      (S : Predicate A) ->
      BorelGenerated reals distance S ->
      measurable events S
    measurable-borel :
      (S : Predicate A) ->
      measurable events S ->
      BorelGenerated reals distance S

preimage :
  {A B : Set} ->
  (A -> B) ->
  Predicate B ->
  Predicate A
preimage f S x =
  S (f x)

MeasurableFunction :
  {A B : Set} ->
  SigmaAlgebra A ->
  SigmaAlgebra B ->
  (A -> B) ->
  Set1
MeasurableFunction source target f =
  (S : Predicate _) ->
  measurable target S ->
  measurable source (preimage f S)

record ContinuousLinearFunctional
  {R E : Set}
  {reals : CompleteOrderedField R}
  (space : NormedVectorSpace R E reals) : Set where
  field
    applyFunctional :
      E -> R
    map-add :
      (x y : E) ->
      applyFunctional (addE space x y) ==
      addR reals (applyFunctional x) (applyFunctional y)
    map-scale :
      (a : R) ->
      (x : E) ->
      applyFunctional (scaleE space a x) ==
      multiplyR reals a (applyFunctional x)
    bounded :
      Exists R
        (\ bound ->
          Both
            (Nonnegative reals bound)
            ((x : E) ->
              lessOrEqualR reals
                (absoluteR reals (applyFunctional x))
                (multiplyR reals bound (normE space x))))

open ContinuousLinearFunctional

positivePart :
  {R : Set} ->
  CompleteOrderedField R ->
  R ->
  R
positivePart reals x =
  divideR reals
    (addR reals (absoluteR reals x) x)
    (fromNatR reals (suc (suc zero)))

negativePart :
  {R : Set} ->
  CompleteOrderedField R ->
  R ->
  R
negativePart reals x =
  divideR reals
    (addR reals (absoluteR reals x) (negateR reals x))
    (fromNatR reals (suc (suc zero)))

record FiniteLowerIntegral
  {A R M : Set}
  {reals : CompleteOrderedField R}
  {events : SigmaAlgebra A}
  (extended : ExtendedNonnegativeReals R M reals)
  (measure : Measure extended events)
  (f : A -> R)
  (value : R) : Set1 where
  field
    value-nonnegative :
      Nonnegative reals value
    lower-integral-finite :
      canonicalLowerIntegral extended measure f ==
      finiteM extended value value-nonnegative

record SignedIntegralValue
  {A R M : Set}
  {reals : CompleteOrderedField R}
  {extended : ExtendedNonnegativeReals R M reals}
  {sourceEvents : SigmaAlgebra A}
  (targetEvents : SigmaAlgebra R)
  (measure : Measure extended sourceEvents)
  (f : A -> R)
  (value : R) : Set1 where
  field
    measurable-integrand :
      MeasurableFunction sourceEvents targetEvents f
    positive-integral negative-integral :
      R
    positive-finite :
      FiniteLowerIntegral extended measure
        (\ x -> positivePart reals (f x))
        positive-integral
    negative-finite :
      FiniteLowerIntegral extended measure
        (\ x -> negativePart reals (f x))
        negative-integral
    signed-integral-equation :
      value ==
      subtractR reals positive-integral negative-integral

IntegrableReal :
  {A R M : Set}
  {reals : CompleteOrderedField R}
  {extended : ExtendedNonnegativeReals R M reals}
  {sourceEvents : SigmaAlgebra A} ->
  SigmaAlgebra R ->
  Measure extended sourceEvents ->
  (A -> R) ->
  Set1
IntegrableReal targetEvents measure f =
  ExistsLarge _
    (\ value ->
      SignedIntegralValue targetEvents measure f value)

gaussianDecay :
  {R : Set} ->
  {reals : CompleteOrderedField R} ->
  RealTranscendentalFunctions reals ->
  R ->
  R ->
  R
gaussianDecay {reals = reals} functions variance t =
  exponential functions
    (negateR reals
      (divideR reals
        (multiplyR reals variance (squareR reals t))
        (fromNatR reals (suc (suc zero)))))

record GaussianProjection
  {R M E : Set}
  {reals : CompleteOrderedField R}
  {extended : ExtendedNonnegativeReals R M reals}
  {space : NormedVectorSpace R E reals}
  {sourceEvents : SigmaAlgebra E}
  (targetEvents : SigmaAlgebra R)
  (functions : RealTranscendentalFunctions reals)
  (measure : Measure extended sourceEvents)
  (functional : ContinuousLinearFunctional space) : Set1 where
  field
    mean variance :
      R
    variance-nonnegative :
      Nonnegative reals variance
    cosine-transform :
      (t : R) ->
      SignedIntegralValue targetEvents measure
        (\ x ->
          cosine functions
            (multiplyR reals t (applyFunctional functional x)))
        (multiplyR reals
          (gaussianDecay functions variance t)
          (cosine functions (multiplyR reals mean t)))
    sine-transform :
      (t : R) ->
      SignedIntegralValue targetEvents measure
        (\ x ->
          sine functions
            (multiplyR reals t (applyFunctional functional x)))
        (multiplyR reals
          (gaussianDecay functions variance t)
          (sine functions (multiplyR reals mean t)))

IsGaussian :
  {R M E : Set}
  {reals : CompleteOrderedField R}
  {extended : ExtendedNonnegativeReals R M reals}
  {space : NormedVectorSpace R E reals}
  {sourceEvents : SigmaAlgebra E} ->
  SigmaAlgebra R ->
  RealTranscendentalFunctions reals ->
  Measure extended sourceEvents ->
  Set1
IsGaussian {space = space} targetEvents functions measure =
  (functional : ContinuousLinearFunctional space) ->
  GaussianProjection targetEvents functions measure functional

exponentialNormSquare :
  {R E : Set}
  {reals : CompleteOrderedField R} ->
  RealTranscendentalFunctions reals ->
  NormedVectorSpace R E reals ->
  R ->
  E ->
  R
exponentialNormSquare {reals = reals} functions space C x =
  exponential functions
    (multiplyR reals C (squareR reals (normE space x)))

ferniques-theorem : Set2
ferniques-theorem =
  (R M E : Set) ->
  (reals : CompleteOrderedField R) ->
  RealNumberPresentation reals ->
  (functions : RealTranscendentalFunctions reals) ->
  (extended : ExtendedNonnegativeReals R M reals) ->
  ENNRealPresentation extended ->
  (space : NormedVectorSpace R E reals) ->
  Complete reals (distanceE space) ->
  SecondCountableMetric reals (distanceE space) ->
  (sourceEvents : SigmaAlgebra E) ->
  BorelSpace reals (distanceE space) sourceEvents ->
  (targetEvents : SigmaAlgebra R) ->
  BorelSpace reals (distanceR reals) targetEvents ->
  (measure : Measure extended sourceEvents) ->
  IsGaussian {space = space} targetEvents functions measure ->
  ExistsLarge R
    (\ C ->
      BothLarge
        (Positive reals C)
        (IntegrableReal targetEvents measure
          (exponentialNormSquare functions space C)))
