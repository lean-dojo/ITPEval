-- Statement-only formalization of thousand-theorems corpus artifact Q137164,
-- "Besicovitch covering theorem": in a second-countable measurable metric
-- space with the Besicovitch property, admissible arbitrarily small closed
-- balls contain a countable disjoint subfamily covering the set almost
-- everywhere. This file contains no proof.

{-# OPTIONS --safe #-}

module Q137164_besicovitch_covering_theorem where

open import Support.Bochner
open import Agda.Builtin.Equality renaming (_≡_ to _==_)
open import Agda.Builtin.Nat using (Nat; zero; suc)

open CompleteOrderedField
open SigmaAlgebra
open ExtendedNonnegativeReals
open Measure

infix 4 _<N_

_<N_ : Nat -> Nat -> Set
m <N n =
  suc m <=N n

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

data Fin : Nat -> Set where
  fzero :
    {n : Nat} ->
    Fin (suc n)
  fsuc :
    {n : Nat} ->
    Fin n ->
    Fin (suc n)

finValue :
  {n : Nat} ->
  Fin n ->
  Nat
finValue fzero =
  zero
finValue (fsuc i) =
  suc (finValue i)

last :
  (n : Nat) ->
  Fin (suc n)
last zero =
  fzero
last (suc n) =
  fsuc (last n)

record MetricSpace
  {R : Set}
  (A : Set)
  (reals : CompleteOrderedField R) : Set1 where
  field
    distance :
      A -> A -> R
    distance-nonnegative :
      (x y : A) ->
      lessOrEqualR reals (zeroR reals) (distance x y)
    distance-self :
      (x : A) ->
      distance x x == zeroR reals
    distance-zero-only :
      (x y : A) ->
      distance x y == zeroR reals ->
      x == y
    distance-symmetric :
      (x y : A) ->
      distance x y == distance y x
    distance-triangle :
      (x y z : A) ->
      lessOrEqualR reals
        (distance x z)
        (addR reals (distance x y) (distance y z))

open MetricSpace

MetricOpen :
  {A R : Set} ->
  {reals : CompleteOrderedField R} ->
  MetricSpace A reals ->
  Predicate A ->
  Set
MetricOpen {A = A} {R = R} {reals = reals} metric U =
  (x : A) ->
  U x ->
  Exists R
    (\ epsilon ->
      Both
        (Positive reals epsilon)
        ((y : A) ->
          StrictLess reals (distance metric y x) epsilon ->
          U y))

record SecondCountableMetric
  {A R : Set}
  {reals : CompleteOrderedField R}
  (metric : MetricSpace A reals) : Set1 where
  field
    basis :
      Nat -> Predicate A
    basis-open :
      (n : Nat) ->
      MetricOpen metric (basis n)
    basis-refines-open :
      (U : Predicate A) ->
      MetricOpen metric U ->
      (x : A) ->
      U x ->
      Exists Nat
        (\ n ->
          Both
            (basis n x)
            (Subset (basis n) U))

OpensMeasurableSpace :
  {A R : Set} ->
  {reals : CompleteOrderedField R} ->
  MetricSpace A reals ->
  SigmaAlgebra A ->
  Set1
OpensMeasurableSpace metric events =
  (U : Predicate _) ->
  MetricOpen metric U ->
  measurable events U

ClosedBall :
  {A R : Set} ->
  {reals : CompleteOrderedField R} ->
  MetricSpace A reals ->
  A ->
  R ->
  Predicate A
ClosedBall {reals = reals} metric center radius point =
  lessOrEqualR reals (distance metric point center) radius

record SatelliteConfig
  {A R : Set}
  {reals : CompleteOrderedField R}
  (metric : MetricSpace A reals)
  (N : Nat)
  (tau : R) : Set1 where
  field
    center :
      Fin (suc N) -> A
    radius :
      Fin (suc N) -> R
    radius-positive :
      (i : Fin (suc N)) ->
      Positive reals (radius i)
    ordered :
      (i j : Fin (suc N)) ->
      i != j ->
      Either
        (Both
          (lessOrEqualR reals
            (radius i)
            (distance metric (center i) (center j)))
          (lessOrEqualR reals
            (radius j)
            (multiplyR reals tau (radius i))))
        (Both
          (lessOrEqualR reals
            (radius j)
            (distance metric (center j) (center i)))
          (lessOrEqualR reals
            (radius i)
            (multiplyR reals tau (radius j))))
    last-ordered :
      (i : Fin (suc N)) ->
      finValue i <N N ->
      Both
        (lessOrEqualR reals
          (radius i)
          (distance metric (center i) (center (last N))))
        (lessOrEqualR reals
          (radius (last N))
          (multiplyR reals tau (radius i)))
    intersects-last :
      (i : Fin (suc N)) ->
      finValue i <N N ->
      lessOrEqualR reals
        (distance metric (center i) (center (last N)))
        (addR reals (radius i) (radius (last N)))

record HasBesicovitchCovering
  {A R : Set}
  {reals : CompleteOrderedField R}
  (metric : MetricSpace A reals) : Set2 where
  field
    satellite-bound :
      Nat
    satellite-factor :
      R
    factor-greater-than-one :
      StrictLess reals
        (oneR reals)
        satellite-factor
    no-satellite-configuration :
      SatelliteConfig metric satellite-bound satellite-factor ->
      Bottom

FiniteMeasure :
  {A R M : Set} ->
  {reals : CompleteOrderedField R} ->
  {extended : ExtendedNonnegativeReals R M reals} ->
  {events : SigmaAlgebra A} ->
  Measure extended events ->
  Set
FiniteMeasure {extended = extended} measure =
  outerMass measure wholeSet != infinityM extended

record SFiniteMeasure
  {A R M : Set}
  {reals : CompleteOrderedField R}
  {extended : ExtendedNonnegativeReals R M reals}
  {events : SigmaAlgebra A}
  (measure : Measure extended events) : Set1 where
  field
    finite-parts :
      Nat -> Measure extended events
    each-part-finite :
      (n : Nat) ->
      FiniteMeasure (finite-parts n)
    parts-sum-to-measure :
      (S : Predicate A) ->
      measurable events S ->
      CountableSum extended
        (\ n -> outerMass (finite-parts n) S)
        (outerMass measure S)

record ElementOf
  {A : Set}
  (S : Predicate A) : Set where
  constructor member
  field
    element :
      A
    membership :
      S element

open ElementOf

record CountableSubset
  {A : Set}
  (S : Predicate A) : Set where
  field
    code :
      ElementOf S -> Nat
    code-injective :
      (x y : ElementOf S) ->
      code x == code y ->
      element x == element y

difference :
  {A : Set} ->
  Predicate A ->
  Predicate A ->
  Predicate A
difference S T x =
  Both (S x) (Not (T x))

BallUnion :
  {A R : Set} ->
  {reals : CompleteOrderedField R} ->
  MetricSpace A reals ->
  Predicate A ->
  (A -> R) ->
  Predicate A
BallUnion {A = A} metric centers radii point =
  Exists A
    (\ center ->
      Both
        (centers center)
        (ClosedBall metric center (radii center) point))

SetPairwiseDisjoint :
  {A : Set} ->
  Predicate A ->
  (A -> Predicate A) ->
  Set
SetPairwiseDisjoint {A = A} indices family =
  (x y : A) ->
  indices x ->
  indices y ->
  x != y ->
  (point : A) ->
  family x point ->
  family y point ->
  Bottom

record BesicovitchCoveringConclusion
  {A R M : Set}
  {reals : CompleteOrderedField R}
  (metric : MetricSpace A reals)
  {events : SigmaAlgebra A}
  {extended : ExtendedNonnegativeReals R M reals}
  (measure : Measure extended events)
  (admissibleRadii : A -> Predicate R)
  (S : Predicate A)
  (upperRadius : A -> R) : Set1 where
  field
    centers :
      Predicate A
    radii :
      A -> R
    centers-countable :
      CountableSubset centers
    centers-in-set :
      Subset centers S
    radii-admissible :
      (x : A) ->
      centers x ->
      Both
        (admissibleRadii x (radii x))
        (Both
          (Positive reals (radii x))
          (StrictLess reals (radii x) (upperRadius x)))
    covers-almost-everywhere :
      outerMass measure
        (difference S (BallUnion metric centers radii))
      ==
      zeroM extended
    closed-balls-pairwise-disjoint :
      SetPairwiseDisjoint centers
        (\ x -> ClosedBall metric x (radii x))

besicovitch-covering-theorem : Set2
besicovitch-covering-theorem =
  (A R M : Set) ->
  (reals : CompleteOrderedField R) ->
  RealNumberPresentation reals ->
  (metric : MetricSpace A reals) ->
  SecondCountableMetric metric ->
  (events : SigmaAlgebra A) ->
  OpensMeasurableSpace metric events ->
  (extended : ExtendedNonnegativeReals R M reals) ->
  (measure : Measure extended events) ->
  SFiniteMeasure measure ->
  HasBesicovitchCovering metric ->
  (admissibleRadii : A -> Predicate R) ->
  (S : Predicate A) ->
  ((x : A) ->
    S x ->
    (delta : R) ->
    Positive reals delta ->
    Exists R
      (\ radius ->
        Both
          (admissibleRadii x radius)
          (Both
            (Positive reals radius)
            (StrictLess reals radius delta)))) ->
  (upperRadius : A -> R) ->
  ((x : A) ->
    S x ->
    Positive reals (upperRadius x)) ->
  BesicovitchCoveringConclusion
    metric measure admissibleRadii S upperRadius
