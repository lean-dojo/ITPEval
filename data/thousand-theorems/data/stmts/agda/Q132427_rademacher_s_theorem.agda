-- Statement-only formalization of thousand-theorems corpus artifact Q132427,
-- "Rademacher's theorem": a Lipschitz map on a measurable subset of a
-- finite-dimensional real normed space is differentiable within that subset
-- almost everywhere for the restricted Haar measure. This file contains no proof.

{-# OPTIONS --safe #-}

module Q132427_rademacher_s_theorem where

open import Support.Bochner
open import Agda.Builtin.Equality renaming (_≡_ to _==_)
open import Agda.Builtin.Nat using (Nat; zero; suc)

open CompleteOrderedField
open NormedVectorSpace
open SigmaAlgebra
open ExtendedNonnegativeReals
open Measure

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
    nonnegative-value :
      R
    value-nonnegative :
      lessOrEqualR reals
        (zeroR reals)
        nonnegative-value

open NonnegativeReal

data Fin : Nat -> Set where
  fzero : {n : Nat} -> Fin (suc n)
  fsuc  : {n : Nat} -> Fin n -> Fin (suc n)

Vector :
  Set ->
  Nat ->
  Set
Vector R n =
  Fin n -> R

VectorEqual :
  {R : Set} ->
  {n : Nat} ->
  Vector R n ->
  Vector R n ->
  Set
VectorEqual {n = n} x y =
  (i : Fin n) -> x i == y i

vectorAdd :
  {R : Set} ->
  {n : Nat} ->
  CompleteOrderedField R ->
  Vector R n ->
  Vector R n ->
  Vector R n
vectorAdd reals x y i =
  addR reals (x i) (y i)

vectorScale :
  {R : Set} ->
  {n : Nat} ->
  CompleteOrderedField R ->
  R ->
  Vector R n ->
  Vector R n
vectorScale reals scalar x i =
  multiplyR reals scalar (x i)

record LinearEquivalence
  {R E : Set}
  (reals : CompleteOrderedField R)
  (space : NormedVectorSpace R E reals)
  (n : Nat) : Set1 where
  field
    forward-linear :
      E -> Vector R n
    backward-linear :
      Vector R n -> E
    forward-after-backward :
      (x : Vector R n) ->
      VectorEqual (forward-linear (backward-linear x)) x
    backward-after-forward :
      (x : E) ->
      backward-linear (forward-linear x) == x
    forward-add :
      (x y : E) ->
      VectorEqual
        (forward-linear (addE space x y))
        (vectorAdd reals (forward-linear x) (forward-linear y))
    forward-scale :
      (a : R) ->
      (x : E) ->
      VectorEqual
        (forward-linear (scaleE space a x))
        (vectorScale reals a (forward-linear x))

record FiniteDimensional
  {R E : Set}
  (reals : CompleteOrderedField R)
  (space : NormedVectorSpace R E reals) : Set1 where
  field
    dimension :
      Nat
    linear-equivalence :
      LinearEquivalence reals space dimension

NormOpen :
  {R E : Set} ->
  {reals : CompleteOrderedField R} ->
  NormedVectorSpace R E reals ->
  Predicate E ->
  Set
NormOpen {R = R} {reals = reals} space U =
  (x : _) ->
  U x ->
  Exists R
    (\ radius ->
      Both
        (Positive reals radius)
        ((y : _) ->
          StrictLess reals (distanceE space y x) radius ->
          U y))

data BorelGenerated
  {R E : Set}
  {reals : CompleteOrderedField R}
  (space : NormedVectorSpace R E reals) :
  Predicate E -> Set1 where
  borel-open :
    {U : Predicate E} ->
    NormOpen space U ->
    BorelGenerated space U
  borel-empty :
    BorelGenerated space emptySet
  borel-complement :
    {S : Predicate E} ->
    BorelGenerated space S ->
    BorelGenerated space (complement S)
  borel-countable-union :
    (sets : Nat -> Predicate E) ->
    ((n : Nat) -> BorelGenerated space (sets n)) ->
    BorelGenerated space (countableUnion sets)
  borel-congruent :
    {S T : Predicate E} ->
    ((x : E) -> Iff (S x) (T x)) ->
    BorelGenerated space S ->
    BorelGenerated space T

record BorelSpace
  {R E : Set}
  {reals : CompleteOrderedField R}
  (space : NormedVectorSpace R E reals)
  (events : SigmaAlgebra E) : Set2 where
  field
    borel-measurable :
      (S : Predicate E) ->
      BorelGenerated space S ->
      measurable events S
    measurable-borel :
      (S : Predicate E) ->
      measurable events S ->
      BorelGenerated space S

data _<N_ : Nat -> Nat -> Set where
  zero<suc :
    {n : Nat} ->
    zero <N suc n
  suc<suc :
    {m n : Nat} ->
    m <N n ->
    suc m <N suc n

StrictlyIncreasing :
  (Nat -> Nat) ->
  Set
StrictlyIncreasing subsequence =
  (m n : Nat) ->
  m <N n ->
  subsequence m <N subsequence n

SequentiallyCompact :
  {R E : Set} ->
  {reals : CompleteOrderedField R} ->
  NormedVectorSpace R E reals ->
  Predicate E ->
  Set
SequentiallyCompact {E = E} {reals = reals} space S =
  (sequence : Nat -> E) ->
  ((n : Nat) -> S (sequence n)) ->
  Exists (Nat -> Nat)
    (\ subsequence ->
      Both
        (StrictlyIncreasing subsequence)
        (Exists E
          (\ limit ->
            Both
              (S limit)
              (SequentialLimit reals (distanceE space)
                (\ n -> sequence (subsequence n))
                limit))))

translateSet :
  {R E : Set} ->
  {reals : CompleteOrderedField R} ->
  NormedVectorSpace R E reals ->
  E ->
  Predicate E ->
  Predicate E
translateSet space shift S x =
  S (subtractE space x shift)

record IsAddHaarMeasure
  {R M E : Set}
  {reals : CompleteOrderedField R}
  (space : NormedVectorSpace R E reals)
  {events : SigmaAlgebra E}
  {extended : ExtendedNonnegativeReals R M reals}
  (measure : Measure extended events) : Set1 where
  field
    translation-invariant :
      (shift : E) ->
      (S : Predicate E) ->
      outerMass measure (translateSet space shift S) ==
      outerMass measure S
    positive-on-nonempty-open :
      (U : Predicate E) ->
      NormOpen space U ->
      Exists E U ->
      outerMass measure U != zeroM extended
    finite-on-compact :
      (K : Predicate E) ->
      SequentiallyCompact space K ->
      outerMass measure K != infinityM extended

LipschitzOnWith :
  {R E F : Set} ->
  {reals : CompleteOrderedField R} ->
  NormedVectorSpace R E reals ->
  NormedVectorSpace R F reals ->
  NonnegativeReal reals ->
  (E -> F) ->
  Predicate E ->
  Set
LipschitzOnWith {reals = reals} source target constant f S =
  (x y : _) ->
  S x ->
  S y ->
  lessOrEqualR reals
    (distanceE target (f x) (f y))
    (multiplyR reals
      (nonnegative-value constant)
      (distanceE source x y))

record ContinuousLinearMap
  {R E F : Set}
  (reals : CompleteOrderedField R)
  (source : NormedVectorSpace R E reals)
  (target : NormedVectorSpace R F reals) : Set where
  field
    linear-map :
      E -> F
    map-add :
      (x y : E) ->
      linear-map (addE source x y) ==
      addE target (linear-map x) (linear-map y)
    map-scale :
      (a : R) ->
      (x : E) ->
      linear-map (scaleE source a x) ==
      scaleE target a (linear-map x)
    operator-bound :
      NonnegativeReal reals
    bounded :
      (x : E) ->
      lessOrEqualR reals
        (normE target (linear-map x))
        (multiplyR reals
          (nonnegative-value operator-bound)
          (normE source x))

open ContinuousLinearMap

DerivativeRemainder :
  {R E F : Set} ->
  {reals : CompleteOrderedField R} ->
  (source : NormedVectorSpace R E reals) ->
  (target : NormedVectorSpace R F reals) ->
  (f : E -> F) ->
  ContinuousLinearMap reals source target ->
  E ->
  E ->
  F
DerivativeRemainder source target f derivative point y =
  subtractE target
    (subtractE target (f y) (f point))
    (linear-map derivative (subtractE source y point))

HasFDerivWithinAt :
  {R E F : Set} ->
  {reals : CompleteOrderedField R} ->
  (source : NormedVectorSpace R E reals) ->
  (target : NormedVectorSpace R F reals) ->
  (f : E -> F) ->
  ContinuousLinearMap reals source target ->
  Predicate E ->
  E ->
  Set
HasFDerivWithinAt {R = R} {reals = reals}
  source target f derivative S point =
  (epsilon : R) ->
  Positive reals epsilon ->
  Exists R
    (\ radius ->
      Both
        (Positive reals radius)
        ((y : _) ->
          S y ->
          StrictLess reals (distanceE source y point) radius ->
          lessOrEqualR reals
            (normE target
              (DerivativeRemainder
                source target f derivative point y))
            (multiplyR reals epsilon
              (distanceE source y point))))

DifferentiableWithinAt :
  {R E F : Set} ->
  {reals : CompleteOrderedField R} ->
  (source : NormedVectorSpace R E reals) ->
  (target : NormedVectorSpace R F reals) ->
  (f : E -> F) ->
  Predicate E ->
  E ->
  Set
DifferentiableWithinAt {reals = reals} source target f S point =
  Exists (ContinuousLinearMap reals source target)
    (\ derivative ->
      HasFDerivWithinAt source target f derivative S point)

AlmostEverywhereOn :
  {R M E : Set} ->
  {reals : CompleteOrderedField R} ->
  {events : SigmaAlgebra E} ->
  {extended : ExtendedNonnegativeReals R M reals} ->
  Measure extended events ->
  Predicate E ->
  Predicate E ->
  Set
AlmostEverywhereOn {extended = extended} measure S property =
  outerMass measure
    (\ x -> Both (S x) (Not (property x))) ==
  zeroM extended

rademacher-s-theorem : Set2
rademacher-s-theorem =
  (R M E F : Set) ->
  (reals : CompleteOrderedField R) ->
  RealNumberPresentation reals ->
  (source : NormedVectorSpace R E reals) ->
  FiniteDimensional reals source ->
  (target : NormedVectorSpace R F reals) ->
  FiniteDimensional reals target ->
  (events : SigmaAlgebra E) ->
  BorelSpace source events ->
  (extended : ExtendedNonnegativeReals R M reals) ->
  (measure : Measure extended events) ->
  IsAddHaarMeasure source measure ->
  (constant : NonnegativeReal reals) ->
  (f : E -> F) ->
  (S : Predicate E) ->
  LipschitzOnWith source target constant f S ->
  measurable events S ->
  AlmostEverywhereOn measure S
    (\ x -> DifferentiableWithinAt source target f S x)
