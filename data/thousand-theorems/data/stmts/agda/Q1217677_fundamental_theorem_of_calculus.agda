-- Statement-only formalization of thousand-theorems corpus artifact Q1217677,
-- "Fundamental theorem of calculus": the almost-everywhere endpoint-limit
-- form of FTC-1 and the Banach-valued right-derivative form of FTC-2.
-- This file contains no proof.

{-# OPTIONS --safe #-}

module Q1217677_fundamental_theorem_of_calculus where

open import Q1067156_dominated_convergence_theorem
open import Agda.Builtin.Equality renaming (_≡_ to _==_)
open import Agda.Builtin.Nat using (Nat)

open CompleteOrderedField
open NormedVectorSpace
open SigmaAlgebra
open ExtendedNonnegativeReals
open Measure

record BochnerIntegration
  {A R M E : Set}
  (reals : CompleteOrderedField R)
  (space : NormedVectorSpace R E reals)
  (events : SigmaAlgebra A)
  (extended : ExtendedNonnegativeReals R M reals)
  (measure : Measure extended events) : Set2 where
  field
    integralVector :
      (A -> E) -> E
    integral-vector-definition :
      (f : A -> E) ->
      TotalizedBochnerIntegralValue
        reals space events extended measure f
        (integralVector f)

open BochnerIntegration

record CompleteOrderedFieldEquivalence
  {R S : Set}
  (source : CompleteOrderedField R)
  (target : CompleteOrderedField S) : Set1 where
  field
    forwardR :
      R -> S
    backwardR :
      S -> R
    forward-after-backwardR :
      (y : S) -> forwardR (backwardR y) == y
    backward-after-forwardR :
      (x : R) -> backwardR (forwardR x) == x
    forward-zeroR :
      forwardR (zeroR source) == zeroR target
    forward-oneR :
      forwardR (oneR source) == oneR target
    forward-addR :
      (x y : R) ->
      forwardR (addR source x y) ==
      addR target (forwardR x) (forwardR y)
    forward-multiplyR :
      (x y : R) ->
      forwardR (multiplyR source x y) ==
      multiplyR target (forwardR x) (forwardR y)
    forward-negateR :
      (x : R) ->
      forwardR (negateR source x) ==
      negateR target (forwardR x)
    forward-reciprocalR :
      (x : R) ->
      forwardR (reciprocalR source x) ==
      reciprocalR target (forwardR x)
    forward-absoluteR :
      (x : R) ->
      forwardR (absoluteR source x) ==
      absoluteR target (forwardR x)
    forward-fromNatR :
      (n : Nat) ->
      forwardR (fromNatR source n) == fromNatR target n
    forward-orderR :
      (x y : R) ->
      Iff
        (lessOrEqualR source x y)
        (lessOrEqualR target (forwardR x) (forwardR y))

record RealNumberPresentation
  {R : Set}
  (reals : CompleteOrderedField R) : Set2 where
  field
    equivalent-complete-ordered-field :
      (S : Set) ->
      (other : CompleteOrderedField S) ->
      CompleteOrderedFieldEquivalence reals other

OpenInterval :
  {R : Set} ->
  CompleteOrderedField R ->
  R ->
  R ->
  Predicate R
OpenInterval reals lower upper point =
  Both
    (StrictLess reals lower point)
    (StrictLess reals point upper)

ClosedInterval :
  {R : Set} ->
  CompleteOrderedField R ->
  R ->
  R ->
  Predicate R
ClosedInterval reals lower upper point =
  Both
    (lessOrEqualR reals lower point)
    (lessOrEqualR reals point upper)

OpenClosedInterval :
  {R : Set} ->
  CompleteOrderedField R ->
  R ->
  R ->
  Predicate R
OpenClosedInterval reals lower upper point =
  Both
    (StrictLess reals lower point)
    (lessOrEqualR reals point upper)

OpenBall :
  {R : Set} ->
  CompleteOrderedField R ->
  R ->
  R ->
  Predicate R
OpenBall reals center radius point =
  StrictLess reals (distanceR reals point center) radius

data BorelGenerated
  {R : Set}
  (reals : CompleteOrderedField R) :
  Predicate R -> Set1 where
  borel-open-interval :
    (lower upper : R) ->
    BorelGenerated reals (OpenInterval reals lower upper)
  borel-empty :
    BorelGenerated reals emptySet
  borel-complement :
    {S : Predicate R} ->
    BorelGenerated reals S ->
    BorelGenerated reals (complement S)
  borel-countable-union :
    (sets : Nat -> Predicate R) ->
    ((n : Nat) -> BorelGenerated reals (sets n)) ->
    BorelGenerated reals (countableUnion sets)
  borel-congruent :
    {S T : Predicate R} ->
    ((x : R) -> Iff (S x) (T x)) ->
    BorelGenerated reals S ->
    BorelGenerated reals T

record BorelLebesguePresentation
  (R M : Set)
  (reals : CompleteOrderedField R) : Set2 where
  field
    events :
      SigmaAlgebra R
    extended :
      ExtendedNonnegativeReals R M reals
    volume :
      Measure extended events
    borel-measurable :
      (S : Predicate R) ->
      BorelGenerated reals S ->
      measurable events S
    measurable-borel :
      (S : Predicate R) ->
      measurable events S ->
      BorelGenerated reals S
    volume-open-interval :
      (lower upper : R) ->
      (ordered : lessOrEqualR reals lower upper) ->
      Exists
        (lessOrEqualR reals
          (zeroR reals)
          (subtractR reals upper lower))
        (\ nonnegative-length ->
          outerMass volume (OpenInterval reals lower upper) ==
          finiteM extended
            (subtractR reals upper lower)
            nonnegative-length)

open BorelLebesguePresentation

record StronglyMeasurableOn
  {R M E : Set}
  (reals : CompleteOrderedField R)
  (space : NormedVectorSpace R E reals)
  (events : SigmaAlgebra R)
  {extended : ExtendedNonnegativeReals R M reals}
  (measure : Measure extended events)
  (f : R -> E)
  (domain : Predicate R) : Set1 where
  field
    extension :
      R -> E
    extension-strongly-measurable :
      StronglyMeasurable reals events (distanceE space) extension
    agrees-on-domain-almost-everywhere :
      AlmostEverywhere measure
        (\ x ->
          domain x ->
          extension x == f x)

record StronglyMeasurableNear
  {R M E : Set}
  (reals : CompleteOrderedField R)
  (space : NormedVectorSpace R E reals)
  (events : SigmaAlgebra R)
  {extended : ExtendedNonnegativeReals R M reals}
  (measure : Measure extended events)
  (f : R -> E)
  (point : R) : Set1 where
  field
    radius :
      R
    radius-positive :
      Positive reals radius
    measurable-on-ball :
      StronglyMeasurableOn
        reals space events measure f
        (OpenBall reals point radius)

AELimitAt :
  {R M E : Set} ->
  (reals : CompleteOrderedField R) ->
  (space : NormedVectorSpace R E reals) ->
  {extended : ExtendedNonnegativeReals R M reals} ->
  {events : SigmaAlgebra R} ->
  Measure extended events ->
  (R -> E) ->
  R ->
  E ->
  Set
AELimitAt reals space measure f point limit =
  (epsilon : _) ->
  Positive reals epsilon ->
  Exists _
    (\ radius ->
      Both
        (Positive reals radius)
        (AlmostEverywhere measure
          (\ x ->
            OpenBall reals point radius x ->
            StrictLess reals
              (distanceE space (f x) limit)
              epsilon)))

ContinuousOn :
  {R E : Set} ->
  (reals : CompleteOrderedField R) ->
  (space : NormedVectorSpace R E reals) ->
  (R -> E) ->
  Predicate R ->
  Set
ContinuousOn reals space f domain =
  (point : _) ->
  domain point ->
  (epsilon : _) ->
  Positive reals epsilon ->
  Exists _
    (\ radius ->
      Both
        (Positive reals radius)
        ((x : _) ->
          domain x ->
          OpenBall reals point radius x ->
          StrictLess reals
            (distanceE space (f x) (f point))
            epsilon))

DerivativeRemainder :
  {R E : Set} ->
  (reals : CompleteOrderedField R) ->
  (space : NormedVectorSpace R E reals) ->
  (R -> E) ->
  E ->
  R ->
  R ->
  E
DerivativeRemainder reals space f derivative x y =
  subtractE space
    (subtractE space (f y) (f x))
    (scaleE space (subtractR reals y x) derivative)

RightDerivativeAt :
  {R E : Set} ->
  (reals : CompleteOrderedField R) ->
  (space : NormedVectorSpace R E reals) ->
  (R -> E) ->
  E ->
  R ->
  Set
RightDerivativeAt reals space f derivative point =
  (epsilon : _) ->
  Positive reals epsilon ->
  Exists _
    (\ radius ->
      Both
        (Positive reals radius)
        ((y : _) ->
          StrictLess reals point y ->
          OpenBall reals point radius y ->
          lessOrEqualR reals
            (normE space
              (DerivativeRemainder
                reals space f derivative point y))
            (multiplyR reals epsilon
              (distanceR reals y point))))

StrictDerivativeAt :
  {R E : Set} ->
  (reals : CompleteOrderedField R) ->
  (space : NormedVectorSpace R E reals) ->
  (R -> E) ->
  E ->
  R ->
  Set
StrictDerivativeAt reals space f derivative point =
  (epsilon : _) ->
  Positive reals epsilon ->
  Exists _
    (\ radius ->
      Both
        (Positive reals radius)
        ((x y : _) ->
          OpenBall reals point radius x ->
          OpenBall reals point radius y ->
          lessOrEqualR reals
            (normE space
              (DerivativeRemainder reals space f derivative x y))
            (multiplyR reals epsilon
              (distanceR reals y x))))

record IntervalCalculus
  {R M E : Set}
  (reals : CompleteOrderedField R)
  (space : NormedVectorSpace R E reals)
  {events : SigmaAlgebra R}
  {extended : ExtendedNonnegativeReals R M reals}
  {measure : Measure extended events}
  (integration :
    BochnerIntegration reals space events extended measure) : Set2 where
  field
    positivePart :
      (R -> E) -> R -> R -> R -> E
    positive-part-on :
      (f : R -> E) ->
      (a b x : R) ->
      OpenClosedInterval reals a b x ->
      positivePart f a b x == f x
    positive-part-off :
      (f : R -> E) ->
      (a b x : R) ->
      Not (OpenClosedInterval reals a b x) ->
      positivePart f a b x == zeroE space

    negativePart :
      (R -> E) -> R -> R -> R -> E
    negative-part-on :
      (f : R -> E) ->
      (a b x : R) ->
      OpenClosedInterval reals b a x ->
      negativePart f a b x == f x
    negative-part-off :
      (f : R -> E) ->
      (a b x : R) ->
      Not (OpenClosedInterval reals b a x) ->
      negativePart f a b x == zeroE space

    intervalIntegral :
      (R -> E) -> R -> R -> E
    interval-integral-definition :
      (f : R -> E) ->
      (a b : R) ->
      intervalIntegral f a b ==
      subtractE space
        (integralVector integration (positivePart f a b))
        (integralVector integration (negativePart f a b))

open IntervalCalculus

record IntervalIntegrable
  {R M E : Set}
  (reals : CompleteOrderedField R)
  (space : NormedVectorSpace R E reals)
  {events : SigmaAlgebra R}
  {extended : ExtendedNonnegativeReals R M reals}
  {measure : Measure extended events}
  (integration :
    BochnerIntegration reals space events extended measure)
  (calculus :
    IntervalCalculus reals space integration)
  (f : R -> E)
  (a b : R) : Set1 where
  field
    positive-integrable :
      VectorIntegrable
        reals space events extended measure
        (positivePart calculus f a b)
    negative-integrable :
      VectorIntegrable
        reals space events extended measure
        (negativePart calculus f a b)

integral-has-strict-derivative-of-ae-limit-right : Set2
integral-has-strict-derivative-of-ae-limit-right =
  (R M E : Set) ->
  (reals : CompleteOrderedField R) ->
  RealNumberPresentation reals ->
  (space : NormedVectorSpace R E reals) ->
  Complete reals (distanceE space) ->
  (lebesgue : BorelLebesguePresentation R M reals) ->
  (integration :
    BochnerIntegration
      reals space
      (events lebesgue)
      (extended lebesgue)
      (volume lebesgue)) ->
  (calculus : IntervalCalculus reals space integration) ->
  (f : R -> E) ->
  (a b : R) ->
  (c : E) ->
  IntervalIntegrable reals space integration calculus f a b ->
  StronglyMeasurableNear
    reals space
    (events lebesgue)
    (volume lebesgue)
    f b ->
  AELimitAt reals space (volume lebesgue) f b c ->
  StrictDerivativeAt reals space
    (\ u -> intervalIntegral calculus f a u)
    c b

integral-equals-subtraction-of-right-derivative : Set2
integral-equals-subtraction-of-right-derivative =
  (R M E : Set) ->
  (reals : CompleteOrderedField R) ->
  RealNumberPresentation reals ->
  (space : NormedVectorSpace R E reals) ->
  Complete reals (distanceE space) ->
  (lebesgue : BorelLebesguePresentation R M reals) ->
  (integration :
    BochnerIntegration
      reals space
      (events lebesgue)
      (extended lebesgue)
      (volume lebesgue)) ->
  (calculus : IntervalCalculus reals space integration) ->
  (f f' : R -> E) ->
  (a b : R) ->
  lessOrEqualR reals a b ->
  ContinuousOn reals space f (ClosedInterval reals a b) ->
  ((x : R) ->
    OpenInterval reals a b x ->
    RightDerivativeAt reals space f (f' x) x) ->
  IntervalIntegrable reals space integration calculus f' a b ->
  intervalIntegral calculus f' a b ==
  subtractE space (f b) (f a)
