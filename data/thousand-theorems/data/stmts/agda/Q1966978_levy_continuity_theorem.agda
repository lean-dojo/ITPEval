-- Statement-only formalization of thousand-theorems corpus artifact Q1966978,
-- "Lévy continuity theorem": weak convergence of probability measures on a
-- finite-dimensional real inner-product space is equivalent to pointwise
-- convergence of their characteristic functions. This file contains no proof.

{-# OPTIONS --safe #-}

module Q1966978_levy_continuity_theorem where

open import Agda.Builtin.Equality renaming (_≡_ to _==_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _*_)

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

SequentialLimit :
  {R A : Set} ->
  CompleteOrderedField R ->
  (A -> A -> R) ->
  (Nat -> A) ->
  A ->
  Set
SequentialLimit reals distance values limit =
  (epsilon : _) ->
  Positive reals epsilon ->
  Exists Nat
    (\ cutoff ->
      (n : Nat) ->
      cutoff <=N n ->
      StrictLess reals (distance (values n) limit) epsilon)

record NormedRealInnerProductSpace
  (R E : Set)
  (reals : CompleteOrderedField R) : Set1 where
  field
    zeroE :
      E
    addE :
      E -> E -> E
    negateE :
      E -> E
    scaleE :
      R -> E -> E
    normE :
      E -> R
    innerE :
      E -> E -> R

    addE-commutative :
      (x y : E) -> addE x y == addE y x
    addE-associative :
      (x y z : E) -> addE (addE x y) z == addE x (addE y z)
    addE-zero :
      (x : E) -> addE x zeroE == x
    addE-inverse :
      (x : E) -> addE x (negateE x) == zeroE
    scaleE-one :
      (x : E) -> scaleE (oneR reals) x == x
    scaleE-multiply :
      (a b : R) ->
      (x : E) ->
      scaleE (multiplyR reals a b) x == scaleE a (scaleE b x)
    scaleE-add-scalars :
      (a b : R) ->
      (x : E) ->
      scaleE (addR reals a b) x == addE (scaleE a x) (scaleE b x)
    scaleE-add-vectors :
      (a : R) ->
      (x y : E) ->
      scaleE a (addE x y) == addE (scaleE a x) (scaleE a y)

    inner-add-left :
      (x y z : E) ->
      innerE (addE x y) z ==
      addR reals (innerE x z) (innerE y z)
    inner-scale-left :
      (a : R) ->
      (x y : E) ->
      innerE (scaleE a x) y ==
      multiplyR reals a (innerE x y)
    inner-symmetric :
      (x y : E) ->
      innerE x y == innerE y x
    inner-nonnegative :
      (x : E) ->
      lessOrEqualR reals (zeroR reals) (innerE x x)
    inner-definite :
      (x : E) ->
      innerE x x == zeroR reals ->
      x == zeroE
    norm-square :
      (x : E) ->
      multiplyR reals (normE x) (normE x) == innerE x x
    norm-nonnegative :
      (x : E) ->
      lessOrEqualR reals (zeroR reals) (normE x)
    norm-triangle :
      (x y : E) ->
      lessOrEqualR reals
        (normE (addE x y))
        (addR reals (normE x) (normE y))

open NormedRealInnerProductSpace

subtractE :
  {R E : Set} ->
  {reals : CompleteOrderedField R} ->
  NormedRealInnerProductSpace R E reals ->
  E ->
  E ->
  E
subtractE space x y =
  addE space x (negateE space y)

distanceE :
  {R E : Set} ->
  {reals : CompleteOrderedField R} ->
  NormedRealInnerProductSpace R E reals ->
  E ->
  E ->
  R
distanceE space x y =
  normE space (subtractE space x y)

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

sumVector :
  {R : Set} ->
  CompleteOrderedField R ->
  (n : Nat) ->
  Vector R n ->
  R
sumVector reals zero terms =
  zeroR reals
sumVector reals (suc n) terms =
  addR reals
    (terms fzero)
    (sumVector reals n (\ i -> terms (fsuc i)))

record FiniteDimensional
  {R E : Set}
  (reals : CompleteOrderedField R)
  (space : NormedRealInnerProductSpace R E reals) : Set1 where
  field
    dimension :
      Nat
    toCoordinates :
      E -> Vector R dimension
    fromCoordinates :
      Vector R dimension -> E
    coordinates-after-vector :
      (x : Vector R dimension) ->
      VectorEqual (toCoordinates (fromCoordinates x)) x
    vector-after-coordinates :
      (x : E) ->
      fromCoordinates (toCoordinates x) == x
    coordinates-add :
      (x y : E) ->
      VectorEqual
        (toCoordinates (addE space x y))
        (\ i -> addR reals (toCoordinates x i) (toCoordinates y i))
    coordinates-scale :
      (a : R) ->
      (x : E) ->
      VectorEqual
        (toCoordinates (scaleE space a x))
        (\ i -> multiplyR reals a (toCoordinates x i))
    coordinates-orthonormal :
      (x y : E) ->
      innerE space x y ==
      sumVector reals dimension
        (\ i ->
          multiplyR reals
            (toCoordinates x i)
            (toCoordinates y i))

NormOpen :
  {R E : Set} ->
  {reals : CompleteOrderedField R} ->
  NormedRealInnerProductSpace R E reals ->
  Predicate E ->
  Set
NormOpen {R = R} {E = E} {reals = reals} space U =
  (x : E) ->
  U x ->
  Exists R
    (\ radius ->
      Both
        (Positive reals radius)
        ((y : E) ->
          StrictLess reals (distanceE space y x) radius ->
          U y))

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

data BorelGenerated
  {R E : Set}
  {reals : CompleteOrderedField R}
  (space : NormedRealInnerProductSpace R E reals) :
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
  (space : NormedRealInnerProductSpace R E reals)
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

PairwiseDisjoint :
  {A : Set} ->
  (Nat -> Predicate A) ->
  Set
PairwiseDisjoint sets =
  (i j : Nat) ->
  i != j ->
  (x : _) ->
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

record ProbabilityMeasure
  {R E : Set}
  (reals : CompleteOrderedField R)
  (events : SigmaAlgebra E) : Set1 where
  field
    mass :
      Predicate E ->
      R
    mass-congruent :
      (S T : Predicate E) ->
      ((x : E) -> Iff (S x) (T x)) ->
      mass S == mass T
    mass-empty :
      mass emptySet == zeroR reals
    mass-nonnegative :
      (S : Predicate E) ->
      lessOrEqualR reals (zeroR reals) (mass S)
    countable-additivity :
      (sets : Nat -> Predicate E) ->
      ((n : Nat) -> measurable events (sets n)) ->
      PairwiseDisjoint sets ->
      SequentialLimit reals
        (\ x y -> absoluteR reals (subtractR reals x y))
        (\ count -> sumFirst reals (\ n -> mass (sets n)) count)
        (mass (countableUnion sets))
    total-mass-one :
      mass wholeSet == oneR reals

open ProbabilityMeasure

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

Bounded :
  {R A : Set} ->
  CompleteOrderedField R ->
  (A -> R) ->
  Set
Bounded {R = R} {A = A} reals f =
  Exists R (\ bound ->
    (x : A) ->
    lessOrEqualR reals (absoluteR reals (f x)) bound)

ContinuousReal :
  {R E : Set} ->
  {reals : CompleteOrderedField R} ->
  NormedRealInnerProductSpace R E reals ->
  (E -> R) ->
  Set
ContinuousReal {R = R} {E = E} {reals = reals} space f =
  (x : E) ->
  (epsilon : R) ->
  Positive reals epsilon ->
  Exists R
    (\ delta ->
      Both
        (Positive reals delta)
        ((y : E) ->
          StrictLess reals (distanceE space y x) delta ->
          StrictLess reals
            (absoluteR reals (subtractR reals (f y) (f x)))
            epsilon))

record BoundedContinuous
  {R E : Set}
  {reals : CompleteOrderedField R}
  (space : NormedRealInnerProductSpace R E reals)
  (f : E -> R) : Set where
  field
    bounded :
      Bounded reals f
    continuous :
      ContinuousReal space f

MetricOpenReal :
  {R : Set} ->
  CompleteOrderedField R ->
  Predicate R ->
  Set
MetricOpenReal {R = R} reals U =
  (x : R) ->
  U x ->
  Exists R
    (\ radius ->
      Both
        (Positive reals radius)
        ((y : R) ->
          StrictLess reals
            (absoluteR reals (subtractR reals y x))
            radius ->
          U y))

BorelMeasurableReal :
  {R E : Set} ->
  CompleteOrderedField R ->
  SigmaAlgebra E ->
  (E -> R) ->
  Set1
BorelMeasurableReal reals events f =
  (U : Predicate _) ->
  MetricOpenReal reals U ->
  measurable events (preimage f U)

record SimpleFunctionBelow
  {R E : Set}
  (reals : CompleteOrderedField R)
  (events : SigmaAlgebra E)
  (f : E -> R) : Set where
  field
    simpleCutoff :
      Nat
    simpleIndex :
      E -> Nat
    simpleValues :
      Nat -> R
    simpleIndexWithin :
      (x : E) ->
      simpleIndex x <=N simpleCutoff
    simpleFiberMeasurable :
      (i : Nat) ->
      i <=N simpleCutoff ->
      measurable events (\ x -> simpleIndex x == i)
    simplePointwiseBelow :
      (x : E) ->
      lessOrEqualR reals (simpleValues (simpleIndex x)) (f x)

open SimpleFunctionBelow

simpleIntegral :
  {R E : Set} ->
  {reals : CompleteOrderedField R} ->
  {events : SigmaAlgebra E} ->
  ProbabilityMeasure reals events ->
  {f : E -> R} ->
  SimpleFunctionBelow reals events f ->
  R
simpleIntegral {reals = reals} measure simple =
  sumFirst reals
    (\ i ->
      multiplyR reals
        (simpleValues simple i)
        (mass measure (\ x -> simpleIndex simple x == i)))
    (suc (simpleCutoff simple))

record SimpleIntegralCandidate
  {R E : Set}
  {reals : CompleteOrderedField R}
  {events : SigmaAlgebra E}
  (measure : ProbabilityMeasure reals events)
  (f : E -> R)
  (candidate : R) : Set where
  field
    candidateSimple :
      SimpleFunctionBelow reals events f
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
  {R E : Set}
  (reals : CompleteOrderedField R)
  (events : SigmaAlgebra E)
  (measure : ProbabilityMeasure reals events)
  (f : E -> R)
  (value : R) : Set1 where
  field
    measurable-function :
      BorelMeasurableReal reals events f
    bounded-function :
      Bounded reals f
    value-is-integral :
      IsSupremum reals
        (\ candidate ->
          SimpleIntegralCandidate measure f candidate)
        value

record RealIntegration
  {R E : Set}
  (reals : CompleteOrderedField R)
  (events : SigmaAlgebra E) : Set2 where
  field
    integral :
      ProbabilityMeasure reals events ->
      (E -> R) ->
      R
    integral-definition :
      (measure : ProbabilityMeasure reals events) ->
      (f : E -> R) ->
      BorelMeasurableReal reals events f ->
      Bounded reals f ->
      LebesgueIntegralValue reals events measure f (integral measure f)
    integral-unique :
      (measure : ProbabilityMeasure reals events) ->
      (f : E -> R) ->
      (value : R) ->
      LebesgueIntegralValue reals events measure f value ->
      integral measure f == value

open RealIntegration

record ComplexNumber (R : Set) : Set where
  constructor complex
  field
    realPart :
      R
    imaginaryPart :
      R

open ComplexNumber

zeroC :
  {R : Set} ->
  CompleteOrderedField R ->
  ComplexNumber R
zeroC reals =
  complex (zeroR reals) (zeroR reals)

oneC :
  {R : Set} ->
  CompleteOrderedField R ->
  ComplexNumber R
oneC reals =
  complex (oneR reals) (zeroR reals)

addC :
  {R : Set} ->
  CompleteOrderedField R ->
  ComplexNumber R ->
  ComplexNumber R ->
  ComplexNumber R
addC reals (complex a b) (complex c d) =
  complex (addR reals a c) (addR reals b d)

negateC :
  {R : Set} ->
  CompleteOrderedField R ->
  ComplexNumber R ->
  ComplexNumber R
negateC reals (complex a b) =
  complex (negateR reals a) (negateR reals b)

subtractC :
  {R : Set} ->
  CompleteOrderedField R ->
  ComplexNumber R ->
  ComplexNumber R ->
  ComplexNumber R
subtractC reals x y =
  addC reals x (negateC reals y)

multiplyC :
  {R : Set} ->
  CompleteOrderedField R ->
  ComplexNumber R ->
  ComplexNumber R ->
  ComplexNumber R
multiplyC reals (complex a b) (complex c d) =
  complex
    (subtractR reals
      (multiplyR reals a c)
      (multiplyR reals b d))
    (addR reals
      (multiplyR reals a d)
      (multiplyR reals b c))

powerC :
  {R : Set} ->
  CompleteOrderedField R ->
  ComplexNumber R ->
  Nat ->
  ComplexNumber R
powerC reals z zero =
  oneC reals
powerC reals z (suc n) =
  multiplyC reals (powerC reals z n) z

factorial :
  Nat ->
  Nat
factorial zero =
  suc zero
factorial (suc n) =
  suc n * factorial n

fromReal :
  {R : Set} ->
  CompleteOrderedField R ->
  R ->
  ComplexNumber R
fromReal reals x =
  complex x (zeroR reals)

complexExponentialTerm :
  {R : Set} ->
  CompleteOrderedField R ->
  ComplexNumber R ->
  Nat ->
  ComplexNumber R
complexExponentialTerm reals z n =
  multiplyC reals
    (powerC reals z n)
    (fromReal reals
      (reciprocalR reals (fromNatR reals (factorial n))))

sumFirstC :
  {R : Set} ->
  CompleteOrderedField R ->
  (Nat -> ComplexNumber R) ->
  Nat ->
  ComplexNumber R
sumFirstC reals terms zero =
  zeroC reals
sumFirstC reals terms (suc n) =
  addC reals (sumFirstC reals terms n) (terms n)

record ComplexAnalysis
  {R : Set}
  (reals : CompleteOrderedField R) : Set1 where
  field
    modulus :
      ComplexNumber R -> R
    modulus-nonnegative :
      (z : ComplexNumber R) ->
      lessOrEqualR reals (zeroR reals) (modulus z)
    modulus-square :
      (z : ComplexNumber R) ->
      multiplyR reals (modulus z) (modulus z) ==
      addR reals
        (multiplyR reals (realPart z) (realPart z))
        (multiplyR reals (imaginaryPart z) (imaginaryPart z))
    expC :
      ComplexNumber R -> ComplexNumber R
    expC-series :
      (z : ComplexNumber R) ->
      SequentialLimit reals
        (\ x y -> modulus (subtractC reals x y))
        (\ n -> sumFirstC reals (complexExponentialTerm reals z) n)
        (expC z)

open ComplexAnalysis

integralC :
  {R E : Set} ->
  {reals : CompleteOrderedField R} ->
  {events : SigmaAlgebra E} ->
  RealIntegration reals events ->
  ProbabilityMeasure reals events ->
  (E -> ComplexNumber R) ->
  ComplexNumber R
integralC integration measure f =
  complex
    (integral integration measure (\ x -> realPart (f x)))
    (integral integration measure (\ x -> imaginaryPart (f x)))

characteristicFunction :
  {R E : Set} ->
  {reals : CompleteOrderedField R} ->
  {events : SigmaAlgebra E} ->
  (space : NormedRealInnerProductSpace R E reals) ->
  (complexAnalysis : ComplexAnalysis reals) ->
  RealIntegration reals events ->
  ProbabilityMeasure reals events ->
  E ->
  ComplexNumber R
characteristicFunction {reals = reals}
  space complexAnalysis integration measure t =
  integralC integration measure
    (\ x ->
      expC complexAnalysis
        (complex
          (zeroR reals)
          (innerE space x t)))

WeakConvergence :
  {R E : Set} ->
  {reals : CompleteOrderedField R} ->
  {events : SigmaAlgebra E} ->
  (space : NormedRealInnerProductSpace R E reals) ->
  RealIntegration reals events ->
  (Nat -> ProbabilityMeasure reals events) ->
  ProbabilityMeasure reals events ->
  Set
WeakConvergence {reals = reals} space integration measures limitMeasure =
  (test : _) ->
  BoundedContinuous space test ->
  SequentialLimit reals
    (\ x y -> absoluteR reals (subtractR reals x y))
    (\ n -> integral integration (measures n) test)
    (integral integration limitMeasure test)

record LevyContext (R E : Set) : Set2 where
  field
    reals :
      CompleteOrderedField R
    space :
      NormedRealInnerProductSpace R E reals
    finite-dimensional :
      FiniteDimensional reals space
    events :
      SigmaAlgebra E
    borel-space :
      BorelSpace space events
    integration :
      RealIntegration reals events
    complex-analysis :
      ComplexAnalysis reals

open LevyContext

levy-continuity-theorem : Set2
levy-continuity-theorem =
  (R E : Set) ->
  (context : LevyContext R E) ->
  (measures :
    Nat -> ProbabilityMeasure (reals context) (events context)) ->
  (limitMeasure :
    ProbabilityMeasure (reals context) (events context)) ->
  Iff
    (WeakConvergence
      (space context)
      (integration context)
      measures
      limitMeasure)
    ((t : E) ->
      SequentialLimit
        (reals context)
        (\ x y ->
          modulus (complex-analysis context)
            (subtractC (reals context) x y))
        (\ n ->
          characteristicFunction
            (space context)
            (complex-analysis context)
            (integration context)
            (measures n)
            t)
        (characteristicFunction
          (space context)
          (complex-analysis context)
          (integration context)
          limitMeasure
          t))
