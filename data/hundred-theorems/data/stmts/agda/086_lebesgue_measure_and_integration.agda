-- Statement-only formalization of corpus artifact hundred-theorems__agda__086,
-- "Lebesgue Measure and Integration": lower Lebesgue integration of ENNReal-valued
-- functions, outer-null almost-everywhere semantics, and set integrals defined by
-- canonical measure restriction on arbitrary measurable spaces. This file contains
-- no proof.

{-# OPTIONS --safe #-}

open import Agda.Builtin.Equality renaming (_≡_ to _==_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)

infix 4 _!=_ _<=N_

data Bottom : Set where

Not : Set -> Set
Not A = A -> Bottom

_!=_ : {A : Set} -> A -> A -> Set
x != y = Not (x == y)

record Top : Set where
  constructor top

record Both (A B : Set) : Set where
  constructor both
  field
    first  : A
    second : B

data Either (A B : Set) : Set where
  left  : A -> Either A B
  right : B -> Either A B

record Iff (A B : Set) : Set where
  constructor equivalence
  field
    forward  : A -> B
    backward : B -> A

record Iff1 (A B : Set1) : Set1 where
  constructor equivalence1
  field
    forward1  : A -> B
    backward1 : B -> A

record Exists (A : Set) (P : A -> Set) : Set where
  constructor witness
  field
    value    : A
    property : P value

record Exists1 (A : Set) (P : A -> Set1) : Set1 where
  constructor witness1
  field
    value1    : A
    property1 : P value1

record Exists2 (A : Set1) (P : A -> Set1) : Set1 where
  constructor witness2
  field
    value2    : A
    property2 : P value2

data _<=N_ : Nat -> Nat -> Set where
  zero<=   : {n : Nat} -> zero <=N n
  suc<=suc : {m n : Nat} -> m <=N n -> suc m <=N suc n

Predicate : Set -> Set1
Predicate A = A -> Set

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

Subset :
  {A : Set} ->
  Predicate A ->
  Predicate A ->
  Set
Subset {A} S T =
  (x : A) -> S x -> T x

PairwiseDisjoint :
  {A : Set} ->
  (Nat -> Predicate A) ->
  Set
PairwiseDisjoint {A} sets =
  (i j : Nat) ->
  i != j ->
  (x : A) ->
  sets i x ->
  sets j x ->
  Bottom

record SigmaAlgebra (A : Set) : Set1 where
  field
    measurable : Predicate A -> Set

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
    measurable-congruent :
      (S T : Predicate A) ->
      ((x : A) -> Iff (S x) (T x)) ->
      measurable S ->
      measurable T

open SigmaAlgebra

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

record CompleteOrderedField (R : Set) : Set1 where
  field
    zeroR oneR : R
    addR multiplyR : R -> R -> R
    negateR reciprocalR : R -> R
    lessOrEqualR : R -> R -> Set
    fromNat : Nat -> R

    one-not-zero :
      oneR != zeroR
    add-commutative :
      (x y : R) -> addR x y == addR y x
    add-associative :
      (x y z : R) ->
      addR (addR x y) z == addR x (addR y z)
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
    multiply-zero :
      (x : R) -> multiplyR x zeroR == zeroR
    distribute :
      (x y z : R) ->
      multiplyR x (addR y z) ==
      addR (multiplyR x y) (multiplyR x z)
    reciprocal-zero :
      reciprocalR zeroR == zeroR
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
    add-nonnegative :
      (x y : R) ->
      lessOrEqualR zeroR x ->
      lessOrEqualR zeroR y ->
      lessOrEqualR zeroR (addR x y)
    zero-less-than-one :
      Both (lessOrEqualR zeroR oneR) (zeroR != oneR)

    fromNat-zero :
      fromNat zero == zeroR
    fromNat-successor :
      (n : Nat) -> fromNat (suc n) == addR (fromNat n) oneR
    fromNat-addition :
      (m n : Nat) ->
      fromNat (m + n) == addR (fromNat m) (fromNat n)
    fromNat-multiplication :
      (m n : Nat) ->
      fromNat (m * n) == multiplyR (fromNat m) (fromNat n)
    fromNat-injective :
      (m n : Nat) -> fromNat m == fromNat n -> m == n

    archimedean :
      (x : R) ->
      Exists Nat (\ n -> lessOrEqualR x (fromNat n))
    least-upper-bound :
      (P : Predicate R) ->
      Exists R P ->
      Exists R
        (\ upper ->
          (x : R) -> P x -> lessOrEqualR x upper) ->
      Exists R
        (\ supremum ->
          Both
            ((x : R) -> P x -> lessOrEqualR x supremum)
            ((upper : R) ->
              ((x : R) -> P x -> lessOrEqualR x upper) ->
              lessOrEqualR supremum upper))

open CompleteOrderedField

record NNReal
  {R : Set}
  (reals : CompleteOrderedField R) : Set where
  constructor nnreal
  field
    realValue : R
    nonnegative :
      lessOrEqualR reals (zeroR reals) realValue

open NNReal

zeroNN :
  {R : Set} ->
  (reals : CompleteOrderedField R) ->
  NNReal reals
zeroNN reals =
  nnreal
    (zeroR reals)
    (order-reflexive reals (zeroR reals))

oneNN :
  {R : Set} ->
  (reals : CompleteOrderedField R) ->
  NNReal reals
oneNN reals =
  nnreal
    (oneR reals)
    (Both.first (zero-less-than-one reals))

addNN :
  {R : Set} ->
  (reals : CompleteOrderedField R) ->
  NNReal reals ->
  NNReal reals ->
  NNReal reals
addNN reals x y =
  nnreal
    (addR reals (realValue x) (realValue y))
    (add-nonnegative reals
      (realValue x)
      (realValue y)
      (nonnegative x)
      (nonnegative y))

multiplyNN :
  {R : Set} ->
  (reals : CompleteOrderedField R) ->
  NNReal reals ->
  NNReal reals ->
  NNReal reals
multiplyNN reals x y =
  nnreal
    (multiplyR reals (realValue x) (realValue y))
    (multiply-nonnegative reals
      (realValue x)
      (realValue y)
      (nonnegative x)
      (nonnegative y))

data ENNReal
  {R : Set}
  (reals : CompleteOrderedField R) : Set where
  finite   : NNReal reals -> ENNReal reals
  infinity : ENNReal reals

zeroE :
  {R : Set} ->
  (reals : CompleteOrderedField R) ->
  ENNReal reals
zeroE reals =
  finite (zeroNN reals)

oneE :
  {R : Set} ->
  (reals : CompleteOrderedField R) ->
  ENNReal reals
oneE reals =
  finite (oneNN reals)

record ENNRealStructure
  {R : Set}
  (reals : CompleteOrderedField R) : Set1 where
  field
    lessOrEqualE : ENNReal reals -> ENNReal reals -> Set
    addE multiplyE : ENNReal reals -> ENNReal reals -> ENNReal reals

    finite-order :
      (x y : NNReal reals) ->
      Iff
        (lessOrEqualE (finite x) (finite y))
        (lessOrEqualR reals (realValue x) (realValue y))
    finite-le-infinity :
      (x : NNReal reals) ->
      lessOrEqualE (finite x) infinity
    infinity-not-le-finite :
      (x : NNReal reals) ->
      Not (lessOrEqualE infinity (finite x))
    infinity-le-infinity :
      lessOrEqualE infinity infinity

    add-finite :
      (x y : NNReal reals) ->
      addE (finite x) (finite y) == finite (addNN reals x y)
    add-infinity-left :
      (x : ENNReal reals) ->
      addE infinity x == infinity
    add-infinity-right :
      (x : ENNReal reals) ->
      addE x infinity == infinity

    multiply-finite :
      (x y : NNReal reals) ->
      multiplyE (finite x) (finite y) ==
      finite (multiplyNN reals x y)
    multiply-infinity-zero-left :
      multiplyE infinity (zeroE reals) == zeroE reals
    multiply-infinity-zero-right :
      multiplyE (zeroE reals) infinity == zeroE reals
    multiply-infinity-positive-left :
      (x : NNReal reals) ->
      realValue x != zeroR reals ->
      multiplyE infinity (finite x) == infinity
    multiply-infinity-positive-right :
      (x : NNReal reals) ->
      realValue x != zeroR reals ->
      multiplyE (finite x) infinity == infinity
    multiply-infinity-infinity :
      multiplyE infinity infinity == infinity

    add-commutative :
      (x y : ENNReal reals) -> addE x y == addE y x
    add-associative :
      (x y z : ENNReal reals) ->
      addE (addE x y) z == addE x (addE y z)
    add-zero :
      (x : ENNReal reals) -> addE x (zeroE reals) == x
    multiply-commutative :
      (x y : ENNReal reals) -> multiplyE x y == multiplyE y x
    multiply-associative :
      (x y z : ENNReal reals) ->
      multiplyE (multiplyE x y) z == multiplyE x (multiplyE y z)
    multiply-one :
      (x : ENNReal reals) -> multiplyE x (oneE reals) == x
    multiply-zero :
      (x : ENNReal reals) -> multiplyE x (zeroE reals) == zeroE reals
    distribute :
      (x y z : ENNReal reals) ->
      multiplyE x (addE y z) ==
      addE (multiplyE x y) (multiplyE x z)

    order-reflexive :
      (x : ENNReal reals) -> lessOrEqualE x x
    order-transitive :
      (x y z : ENNReal reals) ->
      lessOrEqualE x y ->
      lessOrEqualE y z ->
      lessOrEqualE x z
    order-antisymmetric :
      (x y : ENNReal reals) ->
      lessOrEqualE x y ->
      lessOrEqualE y x ->
      x == y
    order-total :
      (x y : ENNReal reals) ->
      Either (lessOrEqualE x y) (lessOrEqualE y x)
    zero-least :
      (x : ENNReal reals) ->
      lessOrEqualE (zeroE reals) x
    infinity-greatest :
      (x : ENNReal reals) ->
      lessOrEqualE x infinity
    add-monotone :
      (w x y z : ENNReal reals) ->
      lessOrEqualE w x ->
      lessOrEqualE y z ->
      lessOrEqualE (addE w y) (addE x z)
    multiply-monotone :
      (w x y z : ENNReal reals) ->
      lessOrEqualE w x ->
      lessOrEqualE y z ->
      lessOrEqualE (multiplyE w y) (multiplyE x z)

    supremum : Predicate (ENNReal reals) -> ENNReal reals
    supremum-upper :
      (P : Predicate (ENNReal reals)) ->
      (x : ENNReal reals) ->
      P x ->
      lessOrEqualE x (supremum P)
    supremum-least :
      (P : Predicate (ENNReal reals)) ->
      (upper : ENNReal reals) ->
      ((x : ENNReal reals) -> P x -> lessOrEqualE x upper) ->
      lessOrEqualE (supremum P) upper

    borelE : SigmaAlgebra (ENNReal reals)
    borel-open-ray :
      (a : ENNReal reals) ->
      measurable borelE
        (\ x -> Both (lessOrEqualE a x) (a != x))
    borel-minimal :
      (candidate : SigmaAlgebra (ENNReal reals)) ->
      ((a : ENNReal reals) ->
        measurable candidate
          (\ x -> Both (lessOrEqualE a x) (a != x))) ->
      (S : Predicate (ENNReal reals)) ->
      measurable borelE S ->
      measurable candidate S
    nonzero-borel :
      measurable borelE (\ x -> x != zeroE reals)

open ENNRealStructure

sumFirst :
  {R : Set} ->
  {reals : CompleteOrderedField R} ->
  ENNRealStructure reals ->
  (Nat -> ENNReal reals) ->
  Nat ->
  ENNReal reals
sumFirst {reals = reals} extended terms zero =
  zeroE reals
sumFirst extended terms (suc n) =
  addE extended (sumFirst extended terms n) (terms n)

sumThrough :
  {R : Set} ->
  {reals : CompleteOrderedField R} ->
  ENNRealStructure reals ->
  (Nat -> ENNReal reals) ->
  Nat ->
  ENNReal reals
sumThrough extended terms zero =
  terms zero
sumThrough extended terms (suc n) =
  addE extended (sumThrough extended terms n) (terms (suc n))

record CountableSumValue
  {R : Set}
  {reals : CompleteOrderedField R}
  (extended : ENNRealStructure reals)
  (terms : Nat -> ENNReal reals)
  (value : ENNReal reals) : Set1 where
  field
    partial-sum-upper :
      (n : Nat) ->
      lessOrEqualE extended (sumFirst extended terms n) value
    least-upper-bound :
      (upper : ENNReal reals) ->
      ((n : Nat) ->
        lessOrEqualE extended (sumFirst extended terms n) upper) ->
      lessOrEqualE extended value upper

record Measure
  {A R : Set}
  {reals : CompleteOrderedField R}
  (extended : ENNRealStructure reals)
  (events : SigmaAlgebra A) : Set1 where
  field
    outerMass : Predicate A -> ENNReal reals

    outer-mass-congruent :
      (S T : Predicate A) ->
      ((x : A) -> Iff (S x) (T x)) ->
      outerMass S == outerMass T
    outer-mass-empty :
      outerMass emptySet == zeroE reals
    outer-mass-monotone :
      (S T : Predicate A) ->
      Subset S T ->
      lessOrEqualE extended (outerMass S) (outerMass T)
    outer-countable-subadditive :
      (sets : Nat -> Predicate A) ->
      (sumValue : ENNReal reals) ->
      CountableSumValue extended
        (\ n -> outerMass (sets n))
        sumValue ->
      lessOrEqualE extended
        (outerMass (countableUnion sets))
        sumValue

    measurable-caratheodory :
      (S : Predicate A) ->
      measurable events S ->
      (T : Predicate A) ->
      outerMass T ==
      addE extended
        (outerMass (intersection T S))
        (outerMass (intersection T (complement S)))
    measurable-countable-additivity :
      (sets : Nat -> Predicate A) ->
      ((n : Nat) -> measurable events (sets n)) ->
      PairwiseDisjoint sets ->
      CountableSumValue extended
        (\ n -> outerMass (sets n))
        (outerMass (countableUnion sets))

open Measure

MeasureLess :
  {A R : Set} ->
  {reals : CompleteOrderedField R} ->
  {extended : ENNRealStructure reals} ->
  {events : SigmaAlgebra A} ->
  Measure extended events ->
  Measure extended events ->
  Set1
MeasureLess {extended = extended} {events = events} measure1 measure2 =
  (S : Predicate _) ->
  measurable events S ->
  lessOrEqualE extended
    (outerMass measure1 S)
    (outerMass measure2 S)

record MeasureRestriction
  {A R : Set}
  {reals : CompleteOrderedField R}
  (extended : ENNRealStructure reals)
  (events : SigmaAlgebra A) : Set1 where
  field
    restrict :
      Measure extended events ->
      Predicate A ->
      Measure extended events
    restrict-outer-mass :
      (measure : Measure extended events) ->
      (S T : Predicate A) ->
      outerMass (restrict measure S) T ==
      outerMass measure (intersection T S)
    restrict-monotone :
      (measure : Measure extended events) ->
      (S T : Predicate A) ->
      Subset S T ->
      MeasureLess (restrict measure S) (restrict measure T)
    restrict-le-self :
      (measure : Measure extended events) ->
      (S : Predicate A) ->
      MeasureLess (restrict measure S) measure

open MeasureRestriction

OuterNull :
  {A R : Set} ->
  {reals : CompleteOrderedField R} ->
  {extended : ENNRealStructure reals} ->
  {events : SigmaAlgebra A} ->
  Measure extended events ->
  Predicate A ->
  Set
OuterNull {reals = reals} measure S =
  outerMass measure S == zeroE reals

AlmostEverywhere :
  {A R : Set} ->
  {reals : CompleteOrderedField R} ->
  {extended : ENNRealStructure reals} ->
  {events : SigmaAlgebra A} ->
  Measure extended events ->
  Predicate A ->
  Set
AlmostEverywhere measure P =
  OuterNull measure (\ x -> Not (P x))

AlmostEqual :
  {A R : Set} ->
  {reals : CompleteOrderedField R} ->
  {extended : ENNRealStructure reals} ->
  {events : SigmaAlgebra A} ->
  Measure extended events ->
  (A -> ENNReal reals) ->
  (A -> ENNReal reals) ->
  Set
AlmostEqual measure f g =
  AlmostEverywhere measure (\ x -> f x == g x)

PointwiseBelow :
  {A R : Set} ->
  {reals : CompleteOrderedField R} ->
  ENNRealStructure reals ->
  (A -> ENNReal reals) ->
  (A -> ENNReal reals) ->
  Set
PointwiseBelow {A} extended f g =
  (x : A) -> lessOrEqualE extended (f x) (g x)

SequenceSupremum :
  {R : Set} ->
  {reals : CompleteOrderedField R} ->
  ENNRealStructure reals ->
  (Nat -> ENNReal reals) ->
  ENNReal reals ->
  Set
SequenceSupremum extended sequence limit =
  Both
    ((n : Nat) -> lessOrEqualE extended (sequence n) limit)
    ((upper : _) ->
      ((n : Nat) -> lessOrEqualE extended (sequence n) upper) ->
      lessOrEqualE extended limit upper)

record SimpleFunction
  {A R : Set}
  {reals : CompleteOrderedField R}
  (events : SigmaAlgebra A) : Set1 where
  field
    function : A -> ENNReal reals
    cutoff : Nat
    values : Nat -> ENNReal reals
    pieces : Nat -> Predicate A

    pieces-measurable :
      (i : Nat) ->
      i <=N cutoff ->
      measurable events (pieces i)
    pieces-disjoint :
      (i j : Nat) ->
      i <=N cutoff ->
      j <=N cutoff ->
      i != j ->
      (x : A) ->
      pieces i x ->
      pieces j x ->
      Bottom
    pieces-cover :
      (x : A) ->
      Exists Nat
        (\ i ->
          Both
            (i <=N cutoff)
            (pieces i x))
    represented-on-pieces :
      (i : Nat) ->
      i <=N cutoff ->
      (x : A) ->
      pieces i x ->
      function x == values i

open SimpleFunction

record SimpleIntegralValue
  {A R : Set}
  {reals : CompleteOrderedField R}
  (extended : ENNRealStructure reals)
  (events : SigmaAlgebra A)
  (measure : Measure extended events)
  (simple : SimpleFunction {R = R} {reals = reals} events)
  (value : ENNReal reals) : Set1 where
  field
    integral-equation :
      value ==
      sumThrough extended
        (\ i ->
          multiplyE extended
            (values simple i)
            (outerMass measure (pieces simple i)))
        (cutoff simple)

record LowerIntegralValue
  {A R : Set}
  {reals : CompleteOrderedField R}
  (extended : ENNRealStructure reals)
  (events : SigmaAlgebra A)
  (measure : Measure extended events)
  (f : A -> ENNReal reals)
  (value : ENNReal reals) : Set1 where
  field
    simple-integrals-below :
      (simple : SimpleFunction {R = R} {reals = reals} events) ->
      PointwiseBelow extended (function simple) f ->
      (simpleValue : ENNReal reals) ->
      SimpleIntegralValue extended events measure simple simpleValue ->
      lessOrEqualE extended simpleValue value
    least-upper-bound :
      (upper : ENNReal reals) ->
      ((simple : SimpleFunction {R = R} {reals = reals} events) ->
        PointwiseBelow extended (function simple) f ->
        (simpleValue : ENNReal reals) ->
        SimpleIntegralValue extended events measure simple simpleValue ->
        lessOrEqualE extended simpleValue upper) ->
      lessOrEqualE extended value upper

record MeasurableLowerEnvelope
  {A R : Set}
  {reals : CompleteOrderedField R}
  (extended : ENNRealStructure reals)
  (events : SigmaAlgebra A)
  (measure : Measure extended events)
  (lowerIntegral :
    Measure extended events ->
    (A -> ENNReal reals) ->
    ENNReal reals)
  (f g : A -> ENNReal reals) : Set1 where
  field
    envelope-measurable :
      MeasurableFunction events (borelE extended) g
    envelope-below :
      PointwiseBelow extended g f
    same-lower-integral :
      lowerIntegral measure f == lowerIntegral measure g

SetLowerIntegral :
  {A R : Set} ->
  {reals : CompleteOrderedField R} ->
  {extended : ENNRealStructure reals} ->
  {events : SigmaAlgebra A} ->
  MeasureRestriction extended events ->
  (Measure extended events ->
    (A -> ENNReal reals) ->
    ENNReal reals) ->
  Measure extended events ->
  Predicate A ->
  (A -> ENNReal reals) ->
  ENNReal reals
SetLowerIntegral restrictions lowerIntegral measure S f =
  lowerIntegral (restrict restrictions measure S) f

record LebesgueIntegration
  {A R : Set}
  {reals : CompleteOrderedField R}
  (extended : ENNRealStructure reals)
  (events : SigmaAlgebra A)
  (restrictions : MeasureRestriction extended events)
  (lowerIntegral :
    Measure extended events ->
    (A -> ENNReal reals) ->
    ENNReal reals) : Set1 where
  field
    lower-integral-definition :
      (measure : Measure extended events) ->
      (f : A -> ENNReal reals) ->
      LowerIntegralValue extended events measure f
        (lowerIntegral measure f)

    measurable-lower-envelope :
      (measure : Measure extended events) ->
      (f : A -> ENNReal reals) ->
      Exists1 (A -> ENNReal reals)
        (\ g ->
          MeasurableLowerEnvelope
            extended events measure lowerIntegral f g)

    indicator :
      Predicate A ->
      (A -> ENNReal reals) ->
      A ->
      ENNReal reals
    indicator-on :
      (S : Predicate A) ->
      (f : A -> ENNReal reals) ->
      (x : A) ->
      S x ->
      indicator S f x == f x
    indicator-off :
      (S : Predicate A) ->
      (f : A -> ENNReal reals) ->
      (x : A) ->
      Not (S x) ->
      indicator S f x == zeroE reals

    lower-integral-congruent :
      (measure : Measure extended events) ->
      (f g : A -> ENNReal reals) ->
      ((x : A) -> f x == g x) ->
      lowerIntegral measure f == lowerIntegral measure g
    lower-integral-congruent-ae :
      (measure : Measure extended events) ->
      (f g : A -> ENNReal reals) ->
      AlmostEqual measure f g ->
      lowerIntegral measure f == lowerIntegral measure g
    lower-integral-monotone :
      (measure : Measure extended events) ->
      (f g : A -> ENNReal reals) ->
      PointwiseBelow extended f g ->
      lessOrEqualE extended
        (lowerIntegral measure f)
        (lowerIntegral measure g)
    lower-integral-monotone-ae :
      (measure : Measure extended events) ->
      (f g : A -> ENNReal reals) ->
      AlmostEverywhere measure
        (\ x -> lessOrEqualE extended (f x) (g x)) ->
      lessOrEqualE extended
        (lowerIntegral measure f)
        (lowerIntegral measure g)
    lower-integral-monotone-measure :
      (measure1 measure2 : Measure extended events) ->
      MeasureLess measure1 measure2 ->
      (f : A -> ENNReal reals) ->
      lessOrEqualE extended
        (lowerIntegral measure1 f)
        (lowerIntegral measure2 f)

    lower-integral-zero :
      (measure : Measure extended events) ->
      lowerIntegral measure (\ _ -> zeroE reals) == zeroE reals
    lower-integral-constant :
      (measure : Measure extended events) ->
      (c : ENNReal reals) ->
      lowerIntegral measure (\ _ -> c) ==
      multiplyE extended c (outerMass measure wholeSet)
    set-lower-integral-constant :
      (measure : Measure extended events) ->
      (S : Predicate A) ->
      (c : ENNReal reals) ->
      SetLowerIntegral restrictions lowerIntegral measure S (\ _ -> c) ==
      multiplyE extended c (outerMass measure S)

    indicator-equals-restricted-integral :
      (measure : Measure extended events) ->
      (S : Predicate A) ->
      measurable events S ->
      (f : A -> ENNReal reals) ->
      lowerIntegral measure (indicator S f) ==
      SetLowerIntegral restrictions lowerIntegral measure S f
    set-integral-monotone :
      (measure : Measure extended events) ->
      (S T : Predicate A) ->
      Subset S T ->
      (f : A -> ENNReal reals) ->
      lessOrEqualE extended
        (SetLowerIntegral restrictions lowerIntegral measure S f)
        (SetLowerIntegral restrictions lowerIntegral measure T f)
    set-integral-le-total :
      (measure : Measure extended events) ->
      (S : Predicate A) ->
      (f : A -> ENNReal reals) ->
      lessOrEqualE extended
        (SetLowerIntegral restrictions lowerIntegral measure S f)
        (lowerIntegral measure f)
    set-integral-countable-additivity :
      (measure : Measure extended events) ->
      (sets : Nat -> Predicate A) ->
      ((n : Nat) -> measurable events (sets n)) ->
      PairwiseDisjoint sets ->
      (f : A -> ENNReal reals) ->
      CountableSumValue extended
        (\ n ->
          SetLowerIntegral restrictions lowerIntegral measure (sets n) f)
        (SetLowerIntegral restrictions lowerIntegral measure
          (countableUnion sets) f)

    lower-integral-monotone-convergence :
      (measure : Measure extended events) ->
      (functions : Nat -> A -> ENNReal reals) ->
      (limitFunction : A -> ENNReal reals) ->
      ((n : Nat) ->
        MeasurableFunction events (borelE extended) (functions n)) ->
      ((n : Nat) ->
        PointwiseBelow extended (functions n) (functions (suc n))) ->
      ((x : A) ->
        SequenceSupremum extended
          (\ n -> functions n x)
          (limitFunction x)) ->
      SequenceSupremum extended
        (\ n -> lowerIntegral measure (functions n))
        (lowerIntegral measure limitFunction)

    lower-integral-zero-iff-ae-zero :
      (measure : Measure extended events) ->
      (f : A -> ENNReal reals) ->
      MeasurableFunction events (borelE extended) f ->
      Iff
        (lowerIntegral measure f == zeroE reals)
        (AlmostEqual measure f (\ _ -> zeroE reals))
    lower-integral-positive-iff-support-positive :
      (measure : Measure extended events) ->
      (f : A -> ENNReal reals) ->
      MeasurableFunction events (borelE extended) f ->
      Iff
        (Both
          (lessOrEqualE extended
            (zeroE reals)
            (lowerIntegral measure f))
          (lowerIntegral measure f != zeroE reals))
        (Both
          (lessOrEqualE extended
            (zeroE reals)
            (outerMass measure (\ x -> f x != zeroE reals)))
          (outerMass measure (\ x -> f x != zeroE reals) != zeroE reals))

    integrals-determine-measurable-mass :
      (measure1 measure2 : Measure extended events) ->
      Iff1
        ((f : A -> ENNReal reals) ->
          MeasurableFunction events (borelE extended) f ->
          lowerIntegral measure1 f == lowerIntegral measure2 f)
        ((S : Predicate A) ->
          measurable events S ->
          outerMass measure1 S == outerMass measure2 S)

lebesgue-measure-and-integration : Set1
lebesgue-measure-and-integration =
  (A R : Set) ->
  (reals : CompleteOrderedField R) ->
  (extended : ENNRealStructure reals) ->
  (events : SigmaAlgebra A) ->
  Exists2
    (MeasureRestriction extended events)
    (\ restrictions ->
      Exists2
        (Measure extended events ->
          (A -> ENNReal reals) ->
          ENNReal reals)
        (\ lowerIntegral ->
          LebesgueIntegration
            extended events restrictions lowerIntegral))
