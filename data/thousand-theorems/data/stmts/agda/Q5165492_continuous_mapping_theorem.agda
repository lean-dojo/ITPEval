-- Statement-only formalization of thousand-theorems corpus artifact Q5165492,
-- "Continuous mapping theorem": continuous images preserve convergence in
-- distribution along an arbitrary filter. This file contains no proof.

{-# OPTIONS --safe #-}

module Q5165492_continuous_mapping_theorem where

open import Agda.Builtin.Equality renaming (_≡_ to _==_)
open import Agda.Builtin.Nat using (Nat; zero; suc)

data Bottom : Set where

Not : Set -> Set
Not A = A -> Bottom

record Top : Set where
  constructor top

record Both (A B : Set) : Set where
  constructor both
  field
    first  : A
    second : B

record BothLarge (A B : Set1) : Set1 where
  constructor both-large
  field
    first-large  : A
    second-large : B

record LiftLarge (A : Set) : Set1 where
  constructor lift-large
  field
    lower-large : A

data Either (A B : Set) : Set where
  left  : A -> Either A B
  right : B -> Either A B

record Iff (A B : Set) : Set where
  constructor equivalence
  field
    forward  : A -> B
    backward : B -> A

record Exists (A : Set) (P : A -> Set) : Set where
  constructor witness
  field
    value    : A
    property : P value

record ExistsLarge (A : Set) (P : A -> Set1) : Set1 where
  constructor witness-large
  field
    value-large    : A
    property-large : P value-large

Predicate : Set -> Set1
Predicate A = A -> Set

Subset :
  {A : Set} ->
  Predicate A ->
  Predicate A ->
  Set
Subset {A = A} S T =
  (x : A) -> S x -> T x

emptySet :
  {A : Set} ->
  Predicate A
emptySet _ =
  Bottom

wholeSet :
  {A : Set} ->
  Predicate A
wholeSet _ =
  Top

complement :
  {A : Set} ->
  Predicate A ->
  Predicate A
complement S x =
  Not (S x)

intersection :
  {A : Set} ->
  Predicate A ->
  Predicate A ->
  Predicate A
intersection S T x =
  Both (S x) (T x)

countableUnion :
  {A : Set} ->
  (Nat -> Predicate A) ->
  Predicate A
countableUnion sets x =
  Exists Nat (\ n -> sets n x)

preimage :
  {A B : Set} ->
  (A -> B) ->
  Predicate B ->
  Predicate A
preimage f S x =
  S (f x)

infix 4 _!=_ _<=N_

_!=_ :
  {A : Set} ->
  A ->
  A ->
  Set
x != y =
  Not (x == y)

data _<=N_ : Nat -> Nat -> Set where
  zero<=   : {n : Nat} -> zero <=N n
  suc<=suc : {m n : Nat} -> m <=N n -> suc m <=N suc n

record CompleteOrderedField (R : Set) : Set1 where
  field
    zeroR oneR : R
    addR multiplyR : R -> R -> R
    negateR reciprocalR absoluteR : R -> R
    lessOrEqualR : R -> R -> Set
    fromNatR : Nat -> R

    one-not-zero :
      oneR != zeroR

    add-commutative :
      (x y : R) -> addR x y == addR y x
    add-associative :
      (x y z : R) -> addR (addR x y) z == addR x (addR y z)
    add-zero :
      (x : R) -> addR x zeroR == x
    add-inverse :
      (x : R) -> addR x (negateR x) == zeroR

    multiply-commutative :
      (x y : R) -> multiplyR x y == multiplyR y x
    multiply-associative :
      (x y z : R) ->
      multiplyR (multiplyR x y) z == multiplyR x (multiplyR y z)
    multiply-one :
      (x : R) -> multiplyR x oneR == x
    distribute :
      (x y z : R) ->
      multiplyR x (addR y z) ==
      addR (multiplyR x y) (multiplyR x z)
    multiply-reciprocal :
      (x : R) ->
      x != zeroR ->
      multiplyR x (reciprocalR x) == oneR

    order-reflexive :
      (x : R) -> lessOrEqualR x x
    order-transitive :
      (x y z : R) ->
      lessOrEqualR x y ->
      lessOrEqualR y z ->
      lessOrEqualR x z
    order-antisymmetric :
      (x y : R) ->
      lessOrEqualR x y ->
      lessOrEqualR y x ->
      x == y
    order-total :
      (x y : R) ->
      Either (lessOrEqualR x y) (lessOrEqualR y x)
    add-order :
      (x y z : R) ->
      lessOrEqualR x y ->
      lessOrEqualR (addR z x) (addR z y)
    multiply-nonnegative :
      (x y : R) ->
      lessOrEqualR zeroR x ->
      lessOrEqualR zeroR y ->
      lessOrEqualR zeroR (multiplyR x y)
    zero-less-than-one :
      Both (lessOrEqualR zeroR oneR) (zeroR != oneR)

    absolute-nonnegative :
      (x : R) ->
      lessOrEqualR zeroR (absoluteR x)
    absolute-of-nonnegative :
      (x : R) ->
      lessOrEqualR zeroR x ->
      absoluteR x == x
    absolute-of-nonpositive :
      (x : R) ->
      lessOrEqualR x zeroR ->
      absoluteR x == negateR x
    absolute-zero-only :
      (x : R) ->
      absoluteR x == zeroR ->
      x == zeroR
    absolute-negate :
      (x : R) ->
      absoluteR (negateR x) == absoluteR x
    absolute-add :
      (x y : R) ->
      lessOrEqualR
        (absoluteR (addR x y))
        (addR (absoluteR x) (absoluteR y))
    absolute-multiply :
      (x y : R) ->
      absoluteR (multiplyR x y) ==
      multiplyR (absoluteR x) (absoluteR y)

    fromNat-zero :
      fromNatR zero == zeroR
    fromNat-successor :
      (n : Nat) ->
      fromNatR (suc n) == addR (fromNatR n) oneR
    fromNat-injective :
      (m n : Nat) ->
      fromNatR m == fromNatR n ->
      m == n

    archimedean :
      (x : R) ->
      Exists Nat (\ n -> lessOrEqualR x (fromNatR n))
    least-upper-bound :
      (P : Predicate R) ->
      Exists R P ->
      Exists R
        (\ upper ->
          (x : R) ->
          P x ->
          lessOrEqualR x upper) ->
      Exists R
        (\ supremum ->
          Both
            ((x : R) ->
              P x ->
              lessOrEqualR x supremum)
            ((upper : R) ->
              ((x : R) ->
                P x ->
                lessOrEqualR x upper) ->
              lessOrEqualR supremum upper))

open CompleteOrderedField

subtractR :
  {R : Set} ->
  CompleteOrderedField R ->
  R ->
  R ->
  R
subtractR reals x y =
  addR reals x (negateR reals y)

distanceR :
  {R : Set} ->
  CompleteOrderedField R ->
  R ->
  R ->
  R
distanceR reals x y =
  absoluteR reals (subtractR reals x y)

StrictLess :
  {R : Set} ->
  CompleteOrderedField R ->
  R ->
  R ->
  Set
StrictLess reals x y =
  Both (lessOrEqualR reals x y) (x != y)

Positive :
  {R : Set} ->
  CompleteOrderedField R ->
  R ->
  Set
Positive reals x =
  StrictLess reals (zeroR reals) x

MetricOpen :
  {R : Set} ->
  CompleteOrderedField R ->
  Predicate R ->
  Set
MetricOpen {R = R} reals U =
  (x : R) ->
  U x ->
  Exists R
    (\ radius ->
      Both
        (Positive reals radius)
        (Subset
          (\ y ->
            StrictLess reals (distanceR reals y x) radius)
          U))

-- The Kuratowski interior presentation is equivalent to specifying all open
-- sets and makes closure under genuinely arbitrary unions derivable from
-- monotonicity, without restricting unions to one fixed index type.
record TopologicalSpace (A : Set) : Set1 where
  field
    interior :
      Predicate A ->
      Predicate A
    interior-subset :
      (U : Predicate A) ->
      Subset (interior U) U
    interior-monotone :
      (U V : Predicate A) ->
      Subset U V ->
      Subset (interior U) (interior V)
    interior-open :
      (U : Predicate A) ->
      Subset (interior U) (interior (interior U))
    interior-whole :
      Subset wholeSet (interior wholeSet)
    interior-intersection :
      (U V : Predicate A) ->
      (x : A) ->
      Iff
        (interior (intersection U V) x)
        (intersection (interior U) (interior V) x)

open TopologicalSpace

openSet :
  {A : Set} ->
  TopologicalSpace A ->
  Predicate A ->
  Set
openSet topology U =
  Subset U (interior topology U)

Continuous :
  {A B : Set} ->
  TopologicalSpace A ->
  TopologicalSpace B ->
  (A -> B) ->
  Set1
Continuous source target f =
  (U : Predicate _) ->
  openSet target U ->
  openSet source (preimage f U)

record SigmaAlgebra (A : Set) : Set1 where
  field
    measurable :
      Predicate A ->
      Set
    measurable-congruent :
      (S T : Predicate A) ->
      ((x : A) -> Iff (S x) (T x)) ->
      measurable S ->
      measurable T
    measurable-empty :
      measurable emptySet
    measurable-complement :
      (S : Predicate A) ->
      measurable S ->
      measurable (complement S)
    measurable-countable-union :
      (sets : Nat -> Predicate A) ->
      ((n : Nat) -> measurable (sets n)) ->
      measurable (countableUnion sets)

open SigmaAlgebra

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

OpensMeasurableSpace :
  {A : Set} ->
  TopologicalSpace A ->
  SigmaAlgebra A ->
  Set1
OpensMeasurableSpace topology events =
  (U : Predicate _) ->
  openSet topology U ->
  measurable events U

data BorelGenerated
  {A : Set}
  (topology : TopologicalSpace A) :
  Predicate A ->
  Set1 where
  borel-open :
    {U : Predicate A} ->
    openSet topology U ->
    BorelGenerated topology U
  borel-empty :
    BorelGenerated topology emptySet
  borel-complement :
    {S : Predicate A} ->
    BorelGenerated topology S ->
    BorelGenerated topology (complement S)
  borel-countable-union :
    (sets : Nat -> Predicate A) ->
    ((n : Nat) -> BorelGenerated topology (sets n)) ->
    BorelGenerated topology (countableUnion sets)
  borel-congruent :
    {S T : Predicate A} ->
    ((x : A) -> Iff (S x) (T x)) ->
    BorelGenerated topology S ->
    BorelGenerated topology T

record BorelSpace
  {A : Set}
  (topology : TopologicalSpace A)
  (events : SigmaAlgebra A) : Set2 where
  field
    borel-measurable :
      (S : Predicate A) ->
      BorelGenerated topology S ->
      measurable events S
    measurable-borel :
      (S : Predicate A) ->
      measurable events S ->
      BorelGenerated topology S

record RealPresentation (R : Set) : Set2 where
  field
    reals :
      CompleteOrderedField R
    topologyR :
      TopologicalSpace R
    borelR :
      SigmaAlgebra R
    borel-presentation :
      BorelSpace topologyR borelR
    topology-is-standard-metric :
      (U : Predicate R) ->
      Iff
        (openSet topologyR U)
        (MetricOpen reals U)

open RealPresentation

record Filter (I : Set) : Set1 where
  field
    eventually :
      Predicate I ->
      Set
    eventually-whole :
      eventually wholeSet
    eventually-upward :
      (P Q : Predicate I) ->
      eventually P ->
      Subset P Q ->
      eventually Q
    eventually-intersection :
      (P Q : Predicate I) ->
      eventually P ->
      eventually Q ->
      eventually (intersection P Q)

open Filter

TendstoReal :
  {I R : Set} ->
  CompleteOrderedField R ->
  Filter I ->
  (I -> R) ->
  R ->
  Set
TendstoReal {R = R} reals sourceFilter values limit =
  (epsilon : R) ->
  Positive reals epsilon ->
  eventually sourceFilter
    (\ i ->
      StrictLess reals
        (distanceR reals (values i) limit)
        epsilon)

SequentialLimit :
  {R : Set} ->
  CompleteOrderedField R ->
  (Nat -> R) ->
  R ->
  Set
SequentialLimit {R = R} reals values limit =
  (epsilon : R) ->
  Positive reals epsilon ->
  Exists Nat
    (\ cutoff ->
      (n : Nat) ->
      cutoff <=N n ->
      StrictLess reals
        (distanceR reals (values n) limit)
        epsilon)

PairwiseDisjoint :
  {A : Set} ->
  (Nat -> Predicate A) ->
  Set
PairwiseDisjoint {A = A} sets =
  (i j : Nat) ->
  i != j ->
  (x : A) ->
  sets i x ->
  sets j x ->
  Bottom

sumFirst :
  {R : Set} ->
  CompleteOrderedField R ->
  (Nat -> R) ->
  Nat ->
  R
sumFirst reals terms zero =
  zeroR reals
sumFirst reals terms (suc n) =
  addR reals (sumFirst reals terms n) (terms n)

record Measure
  {A R : Set}
  (real : RealPresentation R)
  (events : SigmaAlgebra A) : Set1 where
  field
    outerMass :
      Predicate A ->
      R
    outer-mass-congruent :
      (S T : Predicate A) ->
      ((x : A) -> Iff (S x) (T x)) ->
      outerMass S == outerMass T
    outer-mass-empty :
      outerMass emptySet == zeroR (reals real)
    outer-mass-nonnegative :
      (S : Predicate A) ->
      lessOrEqualR (reals real) (zeroR (reals real)) (outerMass S)
    outer-mass-monotone :
      (S T : Predicate A) ->
      Subset S T ->
      lessOrEqualR (reals real) (outerMass S) (outerMass T)
    measurable-caratheodory :
      (S : Predicate A) ->
      measurable events S ->
      (T : Predicate A) ->
      outerMass T ==
      addR (reals real)
        (outerMass (intersection T S))
        (outerMass (intersection T (complement S)))
    measurable-countable-additivity :
      (sets : Nat -> Predicate A) ->
      ((n : Nat) -> measurable events (sets n)) ->
      PairwiseDisjoint sets ->
      SequentialLimit (reals real)
        (\ count ->
          sumFirst (reals real)
            (\ n -> outerMass (sets n))
            count)
        (outerMass (countableUnion sets))

open Measure

record AlmostEverywhere
  {A R : Set}
  {real : RealPresentation R}
  {events : SigmaAlgebra A}
  (measure : Measure real events)
  (property : Predicate A) : Set1 where
  field
    exceptionalSet :
      Predicate A
    exceptionalSetMeasurable :
      measurable events exceptionalSet
    exceptionalSetNull :
      outerMass measure exceptionalSet ==
      zeroR (reals real)
    failuresContainedInExceptionalSet :
      Subset
        (\ x -> Not (property x))
        exceptionalSet

record AEMeasurable
  {A B R : Set}
  {real : RealPresentation R}
  (source : SigmaAlgebra A)
  (target : SigmaAlgebra B)
  (measure : Measure real source)
  (f : A -> B) : Set1 where
  field
    representative :
      A ->
      B
    representative-measurable :
      MeasurableFunction source target representative
    equal-almost-everywhere :
      AlmostEverywhere measure
        (\ x -> f x == representative x)

BoundedFunction :
  {A R : Set} ->
  CompleteOrderedField R ->
  (A -> R) ->
  Set
BoundedFunction {R = R} reals f =
  Exists R
    (\ bound ->
      (x : _) ->
      lessOrEqualR reals (absoluteR reals (f x)) bound)

-- For bounded measurable functions on a finite measure space, the Lebesgue
-- integral is the supremum of the integrals of finite measurable simple
-- functions lying pointwise below the function.
record SimpleFunctionBelow
  {A R : Set}
  (reals : CompleteOrderedField R)
  (events : SigmaAlgebra A)
  (f : A -> R) : Set where
  field
    simpleCutoff :
      Nat
    simpleIndex :
      A ->
      Nat
    simpleValues :
      Nat ->
      R
    simpleIndexWithin :
      (x : A) ->
      simpleIndex x <=N simpleCutoff
    simpleFiberMeasurable :
      (i : Nat) ->
      i <=N simpleCutoff ->
      measurable events (\ x -> simpleIndex x == i)
    simplePointwiseBelow :
      (x : A) ->
      lessOrEqualR reals (simpleValues (simpleIndex x)) (f x)

open SimpleFunctionBelow

simpleIntegral :
  {A R : Set} ->
  {real : RealPresentation R} ->
  {events : SigmaAlgebra A} ->
  (measure : Measure real events) ->
  {f : A -> R} ->
  SimpleFunctionBelow (reals real) events f ->
  R
simpleIntegral {real = real} measure simple =
  sumFirst (reals real)
    (\ i ->
      multiplyR (reals real)
        (simpleValues simple i)
        (outerMass measure
          (\ x -> simpleIndex simple x == i)))
    (suc (simpleCutoff simple))

record SimpleIntegralCandidate
  {A R : Set}
  {real : RealPresentation R}
  {events : SigmaAlgebra A}
  (measure : Measure real events)
  (f : A -> R)
  (candidate : R) : Set where
  field
    candidateSimple :
      SimpleFunctionBelow (reals real) events f
    candidateEquation :
      candidate == simpleIntegral measure candidateSimple

record IsSupremum
  {R : Set}
  (reals : CompleteOrderedField R)
  (P : Predicate R)
  (supremum : R) : Set where
  field
    supremumUpperBound :
      (x : R) ->
      P x ->
      lessOrEqualR reals x supremum
    supremumLeast :
      (upper : R) ->
      ((x : R) ->
        P x ->
        lessOrEqualR reals x upper) ->
      lessOrEqualR reals supremum upper

record LebesgueIntegralValue
  {A R : Set}
  (real : RealPresentation R)
  (events : SigmaAlgebra A)
  (measure : Measure real events)
  (f : A -> R)
  (value : R) : Set1 where
  field
    measurableRepresentative :
      A ->
      R
    representativeMeasurable :
      MeasurableFunction
        events
        (borelR real)
        measurableRepresentative
    representativeEqualAlmostEverywhere :
      AlmostEverywhere measure
        (\ x -> f x == measurableRepresentative x)
    valueIsLebesgueIntegral :
      IsSupremum (reals real)
        (\ candidate ->
          SimpleIntegralCandidate
            measure
            measurableRepresentative
            candidate)
        value

record ProbabilitySpace
  {A R : Set}
  (real : RealPresentation R)
  (events : SigmaAlgebra A) : Set1 where
  field
    probabilityMeasure :
      Measure real events
    total-mass-one :
      outerMass probabilityMeasure wholeSet == oneR (reals real)

open ProbabilitySpace

record BoundedContinuous
  {A R : Set}
  (real : RealPresentation R)
  (topology : TopologicalSpace A)
  (f : A -> R) : Set1 where
  field
    bounded :
      BoundedFunction (reals real) f
    continuous :
      Continuous topology (topologyR real) f

record TendstoInDistribution
  {R I E OmegaPrime : Set}
  (real : RealPresentation R)
  (Omega : I -> Set)
  (sourceEvents : (i : I) -> SigmaAlgebra (Omega i))
  (targetTopology : TopologicalSpace E)
  (targetEvents : SigmaAlgebra E)
  (X : (i : I) -> Omega i -> E)
  (sourceFilter : Filter I)
  (Z : OmegaPrime -> E)
  (limitEvents : SigmaAlgebra OmegaPrime)
  (probabilities :
    (i : I) -> ProbabilitySpace real (sourceEvents i))
  (limitProbability :
    ProbabilitySpace real limitEvents) : Set2 where
  field
    forall-ae-measurable :
      (i : I) ->
      AEMeasurable
        (sourceEvents i)
        targetEvents
        (probabilityMeasure (probabilities i))
        (X i)
    limit-ae-measurable :
      AEMeasurable
        limitEvents
        targetEvents
        (probabilityMeasure limitProbability)
        Z
    weak-convergence-of-laws :
      (test : E -> R) ->
      BoundedContinuous real targetTopology test ->
      ExistsLarge (I -> R)
        (\ integralValues ->
          ExistsLarge R
            (\ limitIntegral ->
              BothLarge
                ((i : I) ->
                  LebesgueIntegralValue
                    real
                    (sourceEvents i)
                    (probabilityMeasure (probabilities i))
                    (\ omega -> test (X i omega))
                    (integralValues i))
                (BothLarge
                  (LebesgueIntegralValue
                    real
                    limitEvents
                    (probabilityMeasure limitProbability)
                    (\ omega -> test (Z omega))
                    limitIntegral)
                  (LiftLarge
                    (TendstoReal (reals real) sourceFilter
                      integralValues
                      limitIntegral)))))

continuous-mapping-theorem : Set2
continuous-mapping-theorem =
  (R I E F OmegaPrime : Set) ->
  (real : RealPresentation R) ->
  (Omega : I -> Set) ->
  (sourceEvents : (i : I) -> SigmaAlgebra (Omega i)) ->
  (limitEvents : SigmaAlgebra OmegaPrime) ->
  (topologyE : TopologicalSpace E) ->
  (eventsE : SigmaAlgebra E) ->
  OpensMeasurableSpace topologyE eventsE ->
  (topologyF : TopologicalSpace F) ->
  (eventsF : SigmaAlgebra F) ->
  BorelSpace topologyF eventsF ->
  (probabilities :
    (i : I) -> ProbabilitySpace real (sourceEvents i)) ->
  (limitProbability : ProbabilitySpace real limitEvents) ->
  (X : (i : I) -> Omega i -> E) ->
  (Z : OmegaPrime -> E) ->
  (sourceFilter : Filter I) ->
  (g : E -> F) ->
  Continuous topologyE topologyF g ->
  TendstoInDistribution
    real
    Omega
    sourceEvents
    topologyE
    eventsE
    X
    sourceFilter
    Z
    limitEvents
    probabilities
    limitProbability ->
  TendstoInDistribution
    real
    Omega
    sourceEvents
    topologyF
    eventsF
    (\ i omega -> g (X i omega))
    sourceFilter
    (\ omega -> g (Z omega))
    limitEvents
    probabilities
    limitProbability
