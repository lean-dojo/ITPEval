-- Statement-only formalization of thousand-theorems corpus artifact Q842953,
-- "Lebesgue's density theorem": in a second-countable Borel metric space with
-- the Besicovitch covering property, almost every point of an arbitrary set is
-- a density point for every locally finite measure. This file contains no proof.

{-# OPTIONS --safe #-}

module Q842953_lebesgue_s_density_theorem where

open import Support.Bochner
open import Agda.Builtin.Equality renaming (_≡_ to _==_)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc)

open CompleteOrderedField
open SigmaAlgebra
open ExtendedNonnegativeReals
open Measure

infix 4 _<N_

record Exists1 (A : Set1) (P : A -> Set) : Set1 where
  constructor witness1
  field
    value1 :
      A
    property1 :
      P value1

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

record NonnegativeReal
  {R : Set}
  (reals : CompleteOrderedField R) : Set where
  constructor nonnegative-real
  field
    realValue :
      R
    realValue-nonnegative :
      lessOrEqualR reals (zeroR reals) realValue

open NonnegativeReal

finiteNN :
  {R M : Set} ->
  {reals : CompleteOrderedField R} ->
  ExtendedNonnegativeReals R M reals ->
  NonnegativeReal reals ->
  M
finiteNN extended x =
  finiteM extended (realValue x) (realValue-nonnegative x)

data CanonicalENNReal
  {R : Set}
  (reals : CompleteOrderedField R) : Set where
  finite-ennreal :
    NonnegativeReal reals ->
    CanonicalENNReal reals
  infinity-ennreal :
    CanonicalENNReal reals

CanonicalENNRealLe :
  {R : Set} ->
  {reals : CompleteOrderedField R} ->
  CanonicalENNReal reals ->
  CanonicalENNReal reals ->
  Set
CanonicalENNRealLe {reals = reals}
  (finite-ennreal x) (finite-ennreal y) =
  lessOrEqualR reals (realValue x) (realValue y)
CanonicalENNRealLe (finite-ennreal x) infinity-ennreal =
  Top
CanonicalENNRealLe infinity-ennreal (finite-ennreal y) =
  Bottom
CanonicalENNRealLe infinity-ennreal infinity-ennreal =
  Top

record ENNRealPresentation
  {R M : Set}
  {reals : CompleteOrderedField R}
  (extended : ExtendedNonnegativeReals R M reals) : Set1 where
  field
    toCanonicalENNReal :
      M -> CanonicalENNReal reals
    fromCanonicalENNReal :
      CanonicalENNReal reals -> M
    to-after-fromENNReal :
      (x : CanonicalENNReal reals) ->
      toCanonicalENNReal (fromCanonicalENNReal x) == x
    from-after-toENNReal :
      (x : M) ->
      fromCanonicalENNReal (toCanonicalENNReal x) == x
    finite-correspondenceENNReal :
      (x : NonnegativeReal reals) ->
      toCanonicalENNReal (finiteNN extended x) == finite-ennreal x
    infinity-correspondenceENNReal :
      toCanonicalENNReal (infinityM extended) == infinity-ennreal
    order-correspondenceENNReal :
      (x y : M) ->
      Iff
        (lessOrEqualM extended x y)
        (CanonicalENNRealLe
          (toCanonicalENNReal x)
          (toCanonicalENNReal y))

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

data BorelGenerated
  {A R : Set}
  {reals : CompleteOrderedField R}
  (metric : MetricSpace A reals) :
  Predicate A -> Set1 where

  borel-open :
    {U : Predicate A} ->
    MetricOpen metric U ->
    BorelGenerated metric U

  borel-empty :
    BorelGenerated metric emptySet

  borel-complement :
    {S : Predicate A} ->
    BorelGenerated metric S ->
    BorelGenerated metric (complement S)

  borel-countable-union :
    (sets : Nat -> Predicate A) ->
    ((n : Nat) -> BorelGenerated metric (sets n)) ->
    BorelGenerated metric (countableUnion sets)

  borel-congruent :
    {S T : Predicate A} ->
    ((x : A) -> Iff (S x) (T x)) ->
    BorelGenerated metric S ->
    BorelGenerated metric T

record BorelSpace
  {A R : Set}
  {reals : CompleteOrderedField R}
  (metric : MetricSpace A reals)
  (events : SigmaAlgebra A) : Set2 where
  field
    borel-measurable :
      (S : Predicate A) ->
      BorelGenerated metric S ->
      measurable events S
    measurable-borel :
      (S : Predicate A) ->
      measurable events S ->
      BorelGenerated metric S

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

record TrimmedMeasure
  {A R M : Set}
  {reals : CompleteOrderedField R}
  {events : SigmaAlgebra A}
  {extended : ExtendedNonnegativeReals R M reals}
  (measure : Measure extended events) : Set2 where
  field
    measurable-envelope :
      (S : Predicate A) ->
      Exists1 (Predicate A)
        (\ T ->
          Both
            (measurable events T)
            (Both
              (Subset S T)
              (outerMass measure S == outerMass measure T)))

IsLocallyFiniteMeasure :
  {A R M : Set} ->
  {reals : CompleteOrderedField R} ->
  {events : SigmaAlgebra A} ->
  {extended : ExtendedNonnegativeReals R M reals} ->
  MetricSpace A reals ->
  Measure extended events ->
  Set
IsLocallyFiniteMeasure {A = A} {R = R} {reals = reals}
  {extended = extended} metric measure =
  (x : A) ->
  Exists R
    (\ radius ->
      Both
        (Positive reals radius)
        (outerMass measure (ClosedBall metric x radius) !=
          infinityM extended))

record MeasureRestriction
  {A R M : Set}
  {reals : CompleteOrderedField R}
  (events : SigmaAlgebra A)
  (extended : ExtendedNonnegativeReals R M reals) : Set2 where
  field
    restrict :
      Measure extended events ->
      Predicate A ->
      Measure extended events
    restrict-on-measurable-test :
      (measure : Measure extended events) ->
      (S T : Predicate A) ->
      measurable events T ->
      outerMass (restrict measure S) T ==
      outerMass measure (intersection T S)
    restrict-trimmed :
      (measure : Measure extended events) ->
      TrimmedMeasure measure ->
      (S : Predicate A) ->
      TrimmedMeasure (restrict measure S)

open MeasureRestriction

record ENNRealReciprocal
  {R M : Set}
  {reals : CompleteOrderedField R}
  (extended : ExtendedNonnegativeReals R M reals) : Set1 where
  field
    reciprocalM :
      M -> M
    reciprocal-zero :
      reciprocalM (zeroM extended) == infinityM extended
    reciprocal-infinity :
      reciprocalM (infinityM extended) == zeroM extended
    reciprocal-finite-zero :
      (x : NonnegativeReal reals) ->
      realValue x == zeroR reals ->
      reciprocalM (finiteNN extended x) == infinityM extended
    reciprocal-finite-positive :
      (x : NonnegativeReal reals) ->
      realValue x != zeroR reals ->
      Exists (NonnegativeReal reals)
        (\ inverse ->
          Both
            (realValue inverse ==
              reciprocalR reals (realValue x))
            (reciprocalM (finiteNN extended x) ==
              finiteNN extended inverse))

open ENNRealReciprocal

divideM :
  {R M : Set} ->
  {reals : CompleteOrderedField R} ->
  (extended : ExtendedNonnegativeReals R M reals) ->
  ENNRealReciprocal extended ->
  M ->
  M ->
  M
divideM extended reciprocal x y =
  multiplyM extended x (reciprocalM reciprocal y)

StrictLessBy :
  {X : Set} ->
  (X -> X -> Set) ->
  X ->
  X ->
  Set
StrictLessBy le x y =
  Both (le x y) (Not (le y x))

data OrderRay (X : Set) : Set where
  above :
    X -> OrderRay X
  below :
    X -> OrderRay X

RayContains :
  {X : Set} ->
  (X -> X -> Set) ->
  OrderRay X ->
  X ->
  Set
RayContains le (above lower) x =
  StrictLessBy le lower x
RayContains le (below upper) x =
  StrictLessBy le x upper

All :
  {X : Set} ->
  (X -> Set) ->
  List X ->
  Set
All P [] =
  Top
All P (x ∷ xs) =
  Both (P x) (All P xs)

BasicContains :
  {X : Set} ->
  (X -> X -> Set) ->
  List (OrderRay X) ->
  X ->
  Set
BasicContains le rays x =
  All (\ ray -> RayContains le ray x) rays

RadiusTendstoM :
  {R M : Set} ->
  {reals : CompleteOrderedField R} ->
  (extended : ExtendedNonnegativeReals R M reals) ->
  (R -> M) ->
  M ->
  Set
RadiusTendstoM {R = R} {reals = reals} extended function limit =
  (rays : List (OrderRay _)) ->
  BasicContains (lessOrEqualM extended) rays limit ->
  Exists R
    (\ delta ->
      Both
        (Positive reals delta)
        ((radius : R) ->
          Positive reals radius ->
          StrictLess reals radius delta ->
          BasicContains
            (lessOrEqualM extended)
            rays
            (function radius)))

lebesgue-density-theorem : Set2
lebesgue-density-theorem =
  (A R M : Set) ->
  (reals : CompleteOrderedField R) ->
  RealNumberPresentation reals ->
  (metric : MetricSpace A reals) ->
  SecondCountableMetric metric ->
  (events : SigmaAlgebra A) ->
  BorelSpace metric events ->
  (extended : ExtendedNonnegativeReals R M reals) ->
  ENNRealPresentation extended ->
  (reciprocal : ENNRealReciprocal extended) ->
  (measure : Measure extended events) ->
  (measure-trimmed : TrimmedMeasure measure) ->
  IsLocallyFiniteMeasure metric measure ->
  (restrictions : MeasureRestriction events extended) ->
  HasBesicovitchCovering metric ->
  (S : Predicate A) ->
  AlmostEverywhere (restrict restrictions measure S)
    (\ x ->
      RadiusTendstoM extended
        (\ radius ->
          divideM extended reciprocal
            (outerMass measure
              (intersection S (ClosedBall metric x radius)))
            (outerMass measure (ClosedBall metric x radius)))
        (oneM extended))
