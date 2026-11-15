-- Statement-only formalization of PutnamBench corpus artifact putnam_2022_a4
-- (putnambench__agda__putnam_2022_a4): the expected weighted sum of independent
-- uniform unit-interval variables stopped at the first failure of strict descent.
-- This file contains no proof.

{-# OPTIONS --safe #-}

module Main where

open import Agda.Builtin.Equality renaming (_≡_ to _==_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)

infix 4 _!=_ _<=N_ _<N_
infixr 3 _and_
infixr 2 _or_

data Bottom : Set where

Not : Set -> Set
Not A =
  A -> Bottom

_!=_ : {A : Set} -> A -> A -> Set
x != y =
  Not (x == y)

record Top : Set where
  constructor top

record _and_ (A B : Set) : Set where
  constructor both
  field
    first  : A
    second : B

data _or_ (A B : Set) : Set where
  left  : A -> A or B
  right : B -> A or B

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

data _<=N_ : Nat -> Nat -> Set where
  zero<=N   : {n : Nat} -> zero <=N n
  suc<=sucN : {m n : Nat} -> m <=N n -> suc m <=N suc n

_<N_ : Nat -> Nat -> Set
m <N n =
  suc m <=N n

data List (A : Set) : Set where
  empty : List A
  cons  : A -> List A -> List A

data Member {A : Set} (x : A) : List A -> Set where
  at-head : {xs : List A} -> Member x (cons x xs)
  in-tail : {y : A} {xs : List A} ->
    Member x xs ->
    Member x (cons y xs)

data NoDuplicates {A : Set} : List A -> Set where
  no-duplicates-empty :
    NoDuplicates empty
  no-duplicates-cons :
    {x : A} {xs : List A} ->
    Not (Member x xs) ->
    NoDuplicates xs ->
    NoDuplicates (cons x xs)

-- An Archimedean complete ordered field is, up to the unique ordered-field
-- isomorphism, the ordinary real line.  Thus later quantification over R does
-- not replace the reals by an arbitrary uninterpreted numeric carrier.
record CompleteOrderedRealField (R : Set) : Set1 where
  field
    zeroR oneR : R
    add multiply : R -> R -> R
    negate inverse : R -> R
    lessOrEqual : R -> R -> Set
    fromNat : Nat -> R

    one-not-zero :
      oneR != zeroR

    add-commutative :
      (x y : R) -> add x y == add y x
    add-associative :
      (x y z : R) ->
      add (add x y) z == add x (add y z)
    add-zero :
      (x : R) -> add x zeroR == x
    add-inverse :
      (x : R) -> add x (negate x) == zeroR

    multiply-commutative :
      (x y : R) -> multiply x y == multiply y x
    multiply-associative :
      (x y z : R) ->
      multiply (multiply x y) z ==
      multiply x (multiply y z)
    multiply-one :
      (x : R) -> multiply x oneR == x
    multiply-zero :
      (x : R) -> multiply x zeroR == zeroR
    distribute :
      (x y z : R) ->
      multiply x (add y z) ==
      add (multiply x y) (multiply x z)
    inverse-zero :
      inverse zeroR == zeroR
    multiply-inverse :
      (x : R) ->
      x != zeroR ->
      multiply x (inverse x) == oneR

    order-reflexive :
      (x : R) -> lessOrEqual x x
    order-transitive :
      (x y z : R) ->
      lessOrEqual x y ->
      lessOrEqual y z ->
      lessOrEqual x z
    order-antisymmetric :
      (x y : R) ->
      lessOrEqual x y ->
      lessOrEqual y x ->
      x == y
    order-total :
      (x y : R) ->
      lessOrEqual x y or lessOrEqual y x
    add-order :
      (x y z : R) ->
      lessOrEqual x y ->
      lessOrEqual (add z x) (add z y)
    multiply-nonnegative :
      (x y : R) ->
      lessOrEqual zeroR x ->
      lessOrEqual zeroR y ->
      lessOrEqual zeroR (multiply x y)
    zero-less-than-one :
      lessOrEqual zeroR oneR and zeroR != oneR

    fromNat-zero :
      fromNat zero == zeroR
    fromNat-successor :
      (n : Nat) ->
      fromNat (suc n) == add (fromNat n) oneR
    fromNat-addition :
      (m n : Nat) ->
      fromNat (m + n) == add (fromNat m) (fromNat n)
    fromNat-multiplication :
      (m n : Nat) ->
      fromNat (m * n) == multiply (fromNat m) (fromNat n)
    fromNat-injective :
      (m n : Nat) ->
      fromNat m == fromNat n ->
      m == n

    archimedean :
      (x : R) ->
      Exists Nat
        (\ n -> lessOrEqual x (fromNat n))
    least-upper-bound :
      (P : R -> Set) ->
      Exists R P ->
      Exists R
        (\ upper ->
          (x : R) ->
          P x ->
          lessOrEqual x upper) ->
      Exists R
        (\ supremum ->
          ((x : R) ->
            P x ->
            lessOrEqual x supremum)
          and
          ((upper : R) ->
            ((x : R) ->
              P x ->
              lessOrEqual x upper) ->
            lessOrEqual supremum upper))

open CompleteOrderedRealField

oneN : Nat
oneN =
  suc zero

twoN : Nat
twoN =
  suc oneN

threeN : Nat
threeN =
  suc twoN

subtract :
  {R : Set} ->
  CompleteOrderedRealField R ->
  R ->
  R ->
  R
subtract reals x y =
  add reals x (negate reals y)

divide :
  {R : Set} ->
  CompleteOrderedRealField R ->
  R ->
  R ->
  R
divide reals x y =
  multiply reals x (inverse reals y)

StrictLess :
  {R : Set} ->
  CompleteOrderedRealField R ->
  R ->
  R ->
  Set
StrictLess reals x y =
  lessOrEqual reals x y and x != y

maximum :
  {R : Set} ->
  CompleteOrderedRealField R ->
  R ->
  R ->
  R
maximum reals x y with order-total reals x y
... | left _ =
  y
... | right _ =
  x

absoluteValue :
  {R : Set} ->
  CompleteOrderedRealField R ->
  R ->
  R
absoluteValue reals x =
  maximum reals x (negate reals x)

CloseTo :
  {R : Set} ->
  CompleteOrderedRealField R ->
  R ->
  R ->
  R ->
  Set
CloseTo reals center radius x =
  StrictLess reals
    (absoluteValue reals (subtract reals x center))
    radius

ConvergesTo :
  {R : Set} ->
  CompleteOrderedRealField R ->
  (Nat -> R) ->
  R ->
  Set
ConvergesTo {R} reals sequence limit =
  (epsilon : R) ->
  StrictLess reals (zeroR reals) epsilon ->
  Exists Nat
    (\ cutoff ->
      (n : Nat) ->
      cutoff <=N n ->
      CloseTo reals limit epsilon (sequence n))

naturalPower :
  {R : Set} ->
  CompleteOrderedRealField R ->
  R ->
  Nat ->
  R
naturalPower reals x zero =
  oneR reals
naturalPower reals x (suc n) =
  multiply reals
    (naturalPower reals x n)
    x

factorial : Nat -> Nat
factorial zero =
  oneN
factorial (suc n) =
  suc n * factorial n

sumFirst :
  {R : Set} ->
  CompleteOrderedRealField R ->
  Nat ->
  (Nat -> R) ->
  R
sumFirst reals zero terms =
  zeroR reals
sumFirst reals (suc n) terms =
  add reals
    (sumFirst reals n terms)
    (terms n)

SeriesHasSum :
  {R : Set} ->
  CompleteOrderedRealField R ->
  (Nat -> R) ->
  R ->
  Set
SeriesHasSum reals terms value =
  ConvergesTo reals
    (\ n -> sumFirst reals n terms)
    value

exponentialTerm :
  {R : Set} ->
  CompleteOrderedRealField R ->
  R ->
  Nat ->
  R
exponentialTerm reals x n =
  divide reals
    (naturalPower reals x n)
    (fromNat reals (factorial n))

-- On a complete ordered real field the everywhere-convergent power series
-- uniquely specifies the ordinary real exponential.
record StandardExponential
  {R : Set}
  (reals : CompleteOrderedRealField R) :
  Set1 where

  field
    exponential : R -> R
    exponential-series :
      (x : R) ->
      SeriesHasSum reals
        (exponentialTerm reals x)
        (exponential x)

open StandardExponential

Predicate : Set -> Set1
Predicate A =
  A -> Set

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
complement E x =
  Not (E x)

countableUnion :
  {A : Set} ->
  (Nat -> Predicate A) ->
  Predicate A
countableUnion sets x =
  Exists Nat (\ n -> sets n x)

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
      (E : Predicate A) ->
      measurable E ->
      measurable (complement E)
    measurable-countable-union :
      (sets : Nat -> Predicate A) ->
      ((n : Nat) -> measurable (sets n)) ->
      measurable (countableUnion sets)
    measurable-congruent :
      (E F : Predicate A) ->
      ((x : A) -> Iff (E x) (F x)) ->
      measurable E ->
      measurable F

open SigmaAlgebra

preimage :
  {A B : Set} ->
  (A -> B) ->
  Predicate B ->
  Predicate A
preimage f E x =
  E (f x)

MeasurableFunction :
  {A B : Set} ->
  SigmaAlgebra A ->
  SigmaAlgebra B ->
  (A -> B) ->
  Set1
MeasurableFunction source target f =
  (E : Predicate _) ->
  measurable target E ->
  measurable source (preimage f E)

record Measure
  {A R : Set}
  (reals : CompleteOrderedRealField R)
  (events : SigmaAlgebra A) :
  Set1 where

  field
    mass : Predicate A -> R

    mass-congruent :
      (E F : Predicate A) ->
      ((x : A) -> Iff (E x) (F x)) ->
      mass E == mass F
    mass-empty :
      mass emptySet == zeroR reals
    mass-nonnegative :
      (E : Predicate A) ->
      measurable events E ->
      lessOrEqual reals (zeroR reals) (mass E)
    countable-additivity :
      (sets : Nat -> Predicate A) ->
      ((n : Nat) -> measurable events (sets n)) ->
      PairwiseDisjoint sets ->
      SeriesHasSum reals
        (\ n -> mass (sets n))
        (mass (countableUnion sets))

open Measure

BoundedFunction :
  {A R : Set} ->
  CompleteOrderedRealField R ->
  (A -> R) ->
  Set
BoundedFunction {A} reals f =
  Exists _
    (\ bound ->
      lessOrEqual reals (zeroR reals) bound
      and
      ((x : A) ->
        lessOrEqual reals
          (absoluteValue reals (f x))
          bound))

PointwiseNonnegative :
  {A R : Set} ->
  CompleteOrderedRealField R ->
  (A -> R) ->
  Set
PointwiseNonnegative {A} reals f =
  (x : A) ->
  lessOrEqual reals (zeroR reals) (f x)

PointwiseIncreasing :
  {A R : Set} ->
  CompleteOrderedRealField R ->
  (Nat -> A -> R) ->
  Set
PointwiseIncreasing {A} reals functions =
  (n : Nat) ->
  (x : A) ->
  lessOrEqual reals
    (functions n x)
    (functions (suc n) x)

NullSet :
  {A R : Set}
  {reals : CompleteOrderedRealField R}
  {events : SigmaAlgebra A} ->
  Measure reals events ->
  Predicate A ->
  Set
NullSet {reals = reals} measure E =
  mass measure E == zeroR reals

AlmostEverywhere :
  {A R : Set}
  {reals : CompleteOrderedRealField R}
  {events : SigmaAlgebra A} ->
  Measure reals events ->
  Predicate A ->
  Set
AlmostEverywhere measure P =
  NullSet measure (\ x -> Not (P x))

AlmostEqual :
  {A R : Set}
  {reals : CompleteOrderedRealField R}
  {events : SigmaAlgebra A} ->
  Measure reals events ->
  (A -> R) ->
  (A -> R) ->
  Set
AlmostEqual measure f g =
  AlmostEverywhere measure (\ x -> f x == g x)

record SimpleFunction
  {A R : Set}
  (reals : CompleteOrderedRealField R)
  (events : SigmaAlgebra A)
  (function : A -> R) :
  Set1 where

  field
    count : Nat
    values : Nat -> R
    pieces : Nat -> Predicate A

    pieces-measurable :
      (i : Nat) ->
      i <N count ->
      measurable events (pieces i)
    pieces-disjoint :
      (i j : Nat) ->
      i <N count ->
      j <N count ->
      i != j ->
      (x : A) ->
      pieces i x ->
      pieces j x ->
      Bottom
    pieces-cover :
      (x : A) ->
      Exists Nat
        (\ i ->
          i <N count
          and
          pieces i x)
    represented-on-pieces :
      (i : Nat) ->
      i <N count ->
      (x : A) ->
      pieces i x ->
      function x == values i

open SimpleFunction

record Integration
  {A R : Set}
  (reals : CompleteOrderedRealField R)
  (realEvents : SigmaAlgebra R)
  (events : SigmaAlgebra A)
  (measure : Measure reals events) :
  Set1 where

  field
    integrable : (A -> R) -> Set
    integral : (A -> R) -> R
    indicator : Predicate A -> A -> R

    integral-congruent :
      (f g : A -> R) ->
      ((x : A) -> f x == g x) ->
      integral f == integral g
    integrable-congruent-ae :
      (f g : A -> R) ->
      AlmostEqual measure f g ->
      Iff (integrable f) (integrable g)
    integral-congruent-ae :
      (f g : A -> R) ->
      AlmostEqual measure f g ->
      integral f == integral g

    indicator-on :
      (E : Predicate A) ->
      (x : A) ->
      E x ->
      indicator E x == oneR reals
    indicator-off :
      (E : Predicate A) ->
      (x : A) ->
      Not (E x) ->
      indicator E x == zeroR reals
    indicator-integrable :
      (E : Predicate A) ->
      measurable events E ->
      integrable (indicator E)
    integral-indicator :
      (E : Predicate A) ->
      measurable events E ->
      integral (indicator E) == mass measure E
    simple-integrable :
      (f : A -> R) ->
      SimpleFunction reals events f ->
      integrable f
    integral-simple :
      (f : A -> R) ->
      (simple : SimpleFunction reals events f) ->
      integral f ==
      sumFirst reals
        (count simple)
        (\ i ->
          multiply reals
            (values simple i)
            (mass measure (pieces simple i)))

    bounded-measurable-integrable :
      (f : A -> R) ->
      MeasurableFunction events realEvents f ->
      BoundedFunction reals f ->
      integrable f

    integral-zero :
      integral (\ _ -> zeroR reals) == zeroR reals
    integral-add :
      (f g : A -> R) ->
      integrable f ->
      integrable g ->
      integral
        (\ x -> add reals (f x) (g x))
      ==
      add reals (integral f) (integral g)
    integral-scale :
      (c : R) ->
      (f : A -> R) ->
      integrable f ->
      integral
        (\ x -> multiply reals c (f x))
      ==
      multiply reals c (integral f)
    integral-nonnegative :
      (f : A -> R) ->
      integrable f ->
      PointwiseNonnegative reals f ->
      lessOrEqual reals (zeroR reals) (integral f)
    integral-nonintegrable-zero :
      (f : A -> R) ->
      Not (integrable f) ->
      integral f == zeroR reals

    monotone-convergence :
      (functions : Nat -> A -> R) ->
      (limitFunction : A -> R) ->
      ((n : Nat) -> integrable (functions n)) ->
      ((n : Nat) -> PointwiseNonnegative reals (functions n)) ->
      PointwiseIncreasing reals functions ->
      ((x : A) ->
        ConvergesTo reals
          (\ n -> functions n x)
          (limitFunction x)) ->
      integrable limitFunction ->
      ConvergesTo reals
        (\ n -> integral (functions n))
        (integral limitFunction)

open Integration

record StandardProbabilityTheory
  (R : Set)
  (reals : CompleteOrderedRealField R) :
  Set1 where

  field
    borel : SigmaAlgebra R
    closed-ray-measurable :
      (a : R) ->
      measurable borel
        (\ x -> lessOrEqual reals x a)
    borel-minimal :
      (candidate : SigmaAlgebra R) ->
      ((a : R) ->
        measurable candidate
          (\ x -> lessOrEqual reals x a)) ->
      (E : Predicate R) ->
      measurable borel E ->
      measurable candidate E

open StandardProbabilityTheory

record ProbabilitySpace
  {A R : Set}
  (reals : CompleteOrderedRealField R)
  (theory : StandardProbabilityTheory R reals)
  (events : SigmaAlgebra A) :
  Set1 where

  field
    measure : Measure reals events
    integration : Integration reals (borel theory) events measure
    total-mass-one :
      mass measure wholeSet == oneR reals

open ProbabilitySpace

probabilityOf :
  {A R : Set}
  {reals : CompleteOrderedRealField R}
  {theory : StandardProbabilityTheory R reals}
  {events : SigmaAlgebra A} ->
  ProbabilitySpace reals theory events ->
  Predicate A ->
  R
probabilityOf space E =
  mass (measure space) E

expectation :
  {A R : Set}
  {reals : CompleteOrderedRealField R}
  {theory : StandardProbabilityTheory R reals}
  {events : SigmaAlgebra A} ->
  ProbabilitySpace reals theory events ->
  (A -> R) ->
  R
expectation space f =
  integral (integration space) f

unitIntervalCDF :
  {R : Set} ->
  CompleteOrderedRealField R ->
  R ->
  R
unitIntervalCDF reals x
  with order-total reals x (zeroR reals)
... | left _ =
  zeroR reals
... | right _ with order-total reals x (oneR reals)
...   | left _ =
  x
...   | right _ =
  oneR reals

UniformOnClosedUnitInterval :
  {A R : Set}
  {reals : CompleteOrderedRealField R}
  {theory : StandardProbabilityTheory R reals}
  {events : SigmaAlgebra A} ->
  ProbabilitySpace reals theory events ->
  (A -> R) ->
  Set
UniformOnClosedUnitInterval {R = R} {reals = reals} space randomVariable =
  (x : R) ->
  probabilityOf space
    (\ outcome ->
      lessOrEqual reals (randomVariable outcome) x)
  ==
  unitIntervalCDF reals x

-- This record makes the standard model explicit: use the ordinary real Borel
-- space with normalized Lebesgue measure on [0,1], and the identity coordinate
-- is Uniform[0,1].  Its fields are exactly the revised probability, Borel, and
-- Lebesgue-integration interfaces above, so the usual model instantiates them.
record StandardUnitIntervalProbabilityModel
  (R : Set)
  (reals : CompleteOrderedRealField R)
  (theory : StandardProbabilityTheory R reals) :
  Set1 where

  field
    unit-space :
      ProbabilitySpace reals theory (borel theory)
    identity-is-measurable :
      MeasurableFunction
        (borel theory)
        (borel theory)
        (\ x -> x)
    identity-is-uniform :
      UniformOnClosedUnitInterval unit-space (\ x -> x)

finiteIntersection :
  {A R : Set} ->
  (Nat -> A -> R) ->
  (Nat -> Predicate R) ->
  List Nat ->
  Predicate A
finiteIntersection X targets empty _ =
  Top
finiteIntersection X targets (cons i indices) outcome =
  targets i (X i outcome)
  and
  finiteIntersection X targets indices outcome

finiteProbabilityProduct :
  {A R : Set}
  {reals : CompleteOrderedRealField R}
  {theory : StandardProbabilityTheory R reals}
  {events : SigmaAlgebra A} ->
  ProbabilitySpace reals theory events ->
  (Nat -> A -> R) ->
  (Nat -> Predicate R) ->
  List Nat ->
  R
finiteProbabilityProduct {reals = reals} space X targets empty =
  oneR reals
finiteProbabilityProduct {reals = reals} space X targets
  (cons i indices) =
  multiply reals
    (probabilityOf space (preimage (X i) (targets i)))
    (finiteProbabilityProduct space X targets indices)

IndependentRandomVariables :
  {A R : Set}
  {reals : CompleteOrderedRealField R}
  {theory : StandardProbabilityTheory R reals}
  {events : SigmaAlgebra A} ->
  ProbabilitySpace reals theory events ->
  (Nat -> A -> R) ->
  Set1
IndependentRandomVariables
  {R = R} {reals = reals} {theory = theory}
  space X =
  (indices : List Nat) ->
  NoDuplicates indices ->
  (targets : Nat -> Predicate R) ->
  ((i : Nat) ->
    Member i indices ->
    measurable (borel theory) (targets i)) ->
  probabilityOf space
    (finiteIntersection X targets indices)
  ==
  finiteProbabilityProduct space X targets indices

StoppingIndexSet :
  {A R : Set} ->
  CompleteOrderedRealField R ->
  (Nat -> A -> R) ->
  (A -> Predicate Nat) ->
  Set
StoppingIndexSet {A} reals X k =
  (outcome : A) ->
  (n : Nat) ->
  Iff
    (k outcome n)
    (Exists Nat
      (\ m ->
        n <=N m
        and
        ((l : Nat) ->
          l <N m ->
          StrictLess reals
            (X (suc l) outcome)
            (X l outcome))))

InitialSegmentSeriesValue :
  {R : Set} ->
  CompleteOrderedRealField R ->
  Predicate Nat ->
  (Nat -> R) ->
  R ->
  Set
InitialSegmentSeriesValue reals indices terms value =
  (Exists Nat
    (\ last ->
      ((n : Nat) ->
        Iff (indices n) (n <=N last))
      and
      value ==
      sumFirst reals (suc last) terms))
  or
  (((n : Nat) -> indices n)
  and
  SeriesHasSum reals terms value)

weightedTerm :
  {A R : Set} ->
  CompleteOrderedRealField R ->
  (Nat -> A -> R) ->
  A ->
  Nat ->
  R
weightedTerm reals X outcome i =
  divide reals
    (X i outcome)
    (naturalPower reals
      (fromNat reals twoN)
      (suc i))

StoppedWeightedSum :
  {A R : Set} ->
  CompleteOrderedRealField R ->
  (Nat -> A -> R) ->
  (A -> Predicate Nat) ->
  (A -> R) ->
  Set
StoppedWeightedSum {A} reals X k S =
  (outcome : A) ->
  InitialSegmentSeriesValue reals
    (k outcome)
    (weightedTerm reals X outcome)
    (S outcome)

putnam-2022-a4-solution :
  {R : Set} ->
  (reals : CompleteOrderedRealField R) ->
  StandardExponential reals ->
  R
putnam-2022-a4-solution reals analysis =
  subtract reals
    (multiply reals
      (fromNat reals twoN)
      (exponential analysis
        (divide reals
          (oneR reals)
          (fromNat reals twoN))))
    (fromNat reals threeN)

putnam-2022-a4 : Set1
putnam-2022-a4 =
  (R : Set) ->
  (reals : CompleteOrderedRealField R) ->
  (analysis : StandardExponential reals) ->
  (A : Set) ->
  (theory : StandardProbabilityTheory R reals) ->
  (events : SigmaAlgebra A) ->
  (space : ProbabilitySpace reals theory events) ->
  (X : Nat -> A -> R) ->
  ((i : Nat) ->
    MeasurableFunction events (borel theory) (X i)) ->
  ((i : Nat) ->
    UniformOnClosedUnitInterval space (X i)) ->
  IndependentRandomVariables space X ->
  (k : A -> Predicate Nat) ->
  StoppingIndexSet reals X k ->
  (S : A -> R) ->
  StoppedWeightedSum reals X k S ->
  expectation space S ==
  putnam-2022-a4-solution reals analysis
