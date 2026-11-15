-- Statement-only formalization of Hundred Theorems artifact 059, "The Laws of Large Numbers":
-- the strong law for pairwise-independent, identically distributed, integrable real random variables,
-- whose sample averages converge almost surely to their common expectation.
-- This file contains no proof.

module LawsOfLargeNumbers where

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

record Exists (A : Set) (P : A -> Set) : Set where
  constructor witness
  field
    value    : A
    property : P value

data _<=N_ : Nat -> Nat -> Set where
  zero<=   : {n : Nat} -> zero <=N n
  suc<=suc : {m n : Nat} -> m <=N n -> suc m <=N suc n

data List (A : Set) : Set where
  empty : List A
  cons  : A -> List A -> List A

data Member {A : Set} (x : A) : List A -> Set where
  at-head : {xs : List A} -> Member x (cons x xs)
  in-tail : {y : A} {xs : List A} -> Member x xs -> Member x (cons y xs)

data NoDuplicates {A : Set} : List A -> Set where
  no-duplicates-empty :
    NoDuplicates empty
  no-duplicates-cons :
    {x : A} {xs : List A} ->
    Not (Member x xs) ->
    NoDuplicates xs ->
    NoDuplicates (cons x xs)

record CompleteOrderedField (R : Set) : Set1 where
  field
    zeroR oneR : R
    add multiply : R -> R -> R
    negate reciprocal absoluteValue : R -> R
    lessOrEqual : R -> R -> Set
    fromNat : Nat -> R

    one-not-zero :
      oneR != zeroR

    add-commutative :
      (x y : R) -> add x y == add y x
    add-associative :
      (x y z : R) -> add (add x y) z == add x (add y z)
    add-zero :
      (x : R) -> add x zeroR == x
    add-inverse :
      (x : R) -> add x (negate x) == zeroR

    multiply-commutative :
      (x y : R) -> multiply x y == multiply y x
    multiply-associative :
      (x y z : R) ->
      multiply (multiply x y) z == multiply x (multiply y z)
    multiply-one :
      (x : R) -> multiply x oneR == x
    multiply-zero :
      (x : R) -> multiply x zeroR == zeroR
    distribute :
      (x y z : R) ->
      multiply x (add y z) ==
      add (multiply x y) (multiply x z)
    reciprocal-zero :
      reciprocal zeroR == zeroR
    multiply-reciprocal :
      (x : R) ->
      x != zeroR ->
      multiply x (reciprocal x) == oneR

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
      Either (lessOrEqual x y) (lessOrEqual y x)
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
      Both (lessOrEqual zeroR oneR) (zeroR != oneR)

    fromNat-zero :
      fromNat zero == zeroR
    fromNat-successor :
      (n : Nat) -> fromNat (suc n) == add (fromNat n) oneR
    fromNat-addition :
      (m n : Nat) ->
      fromNat (m + n) == add (fromNat m) (fromNat n)
    fromNat-multiplication :
      (m n : Nat) ->
      fromNat (m * n) == multiply (fromNat m) (fromNat n)
    fromNat-injective :
      (m n : Nat) -> fromNat m == fromNat n -> m == n

    absolute-of-nonnegative :
      (x : R) ->
      lessOrEqual zeroR x ->
      absoluteValue x == x
    absolute-of-nonpositive :
      (x : R) ->
      lessOrEqual x zeroR ->
      absoluteValue x == negate x

    archimedean :
      (x : R) ->
      Exists Nat (\ n -> lessOrEqual x (fromNat n))
    least-upper-bound :
      (P : R -> Set) ->
      Exists R P ->
      Exists R
        (\ upper ->
          (x : R) -> P x -> lessOrEqual x upper) ->
      Exists R
        (\ supremum ->
          Both
            ((x : R) -> P x -> lessOrEqual x supremum)
            ((upper : R) ->
              ((x : R) -> P x -> lessOrEqual x upper) ->
              lessOrEqual supremum upper))

open CompleteOrderedField

subtract :
  {R : Set} ->
  CompleteOrderedField R ->
  R ->
  R ->
  R
subtract reals x y =
  add reals x (negate reals y)

divide :
  {R : Set} ->
  CompleteOrderedField R ->
  R ->
  R ->
  R
divide reals x y =
  multiply reals x (reciprocal reals y)

square :
  {R : Set} ->
  CompleteOrderedField R ->
  R ->
  R
square reals x =
  multiply reals x x

StrictLess :
  {R : Set} ->
  CompleteOrderedField R ->
  R ->
  R ->
  Set
StrictLess reals x y =
  Both (lessOrEqual reals x y) (x != y)

Close :
  {R : Set} ->
  CompleteOrderedField R ->
  R ->
  R ->
  R ->
  Set
Close reals center radius x =
  StrictLess reals
    (absoluteValue reals (subtract reals x center))
    radius

SequentialLimit :
  {R : Set} ->
  CompleteOrderedField R ->
  (Nat -> R) ->
  R ->
  Set
SequentialLimit {R} reals sequence limit =
  (epsilon : R) ->
  StrictLess reals (zeroR reals) epsilon ->
  Exists Nat
    (\ cutoff ->
      (n : Nat) ->
      cutoff <=N n ->
      StrictLess reals
        (absoluteValue reals (subtract reals (sequence n) limit))
        epsilon)

BoundedFunction :
  {A R : Set} ->
  CompleteOrderedField R ->
  (A -> R) ->
  Set
BoundedFunction {A} {R} reals f =
  Exists R
    (\ bound ->
      Both
        (lessOrEqual reals (zeroR reals) bound)
        ((x : A) ->
          lessOrEqual reals
            (absoluteValue reals (f x))
            bound))

Continuous :
  {R : Set} ->
  CompleteOrderedField R ->
  (R -> R) ->
  Set
Continuous {R} reals f =
  (x epsilon : R) ->
  StrictLess reals (zeroR reals) epsilon ->
  Exists R
    (\ delta ->
      Both
        (StrictLess reals (zeroR reals) delta)
        ((y : R) ->
          Close reals x delta y ->
          Close reals (f x) epsilon (f y)))

record BoundedContinuous
  {R : Set}
  (reals : CompleteOrderedField R)
  (f : R -> R) : Set where
  field
    bounded    : BoundedFunction reals f
    continuous : Continuous reals f

power :
  {R : Set} ->
  CompleteOrderedField R ->
  R ->
  Nat ->
  R
power reals x zero =
  oneR reals
power reals x (suc n) =
  multiply reals (power reals x n) x

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
  negate reals (alternatingSign reals n)

evenIndex : Nat -> Nat
evenIndex n =
  n + n

oddIndex : Nat -> Nat
oddIndex n =
  suc (evenIndex n)

sumFirst :
  {R : Set} ->
  CompleteOrderedField R ->
  (Nat -> R) ->
  Nat ->
  R
sumFirst reals term zero =
  zeroR reals
sumFirst reals term (suc n) =
  add reals
    (sumFirst reals term n)
    (term n)

exponentialPartialSum :
  {R : Set} ->
  CompleteOrderedField R ->
  R ->
  Nat ->
  R
exponentialPartialSum reals x n =
  sumFirst reals
    (\ k ->
      divide reals
        (power reals x k)
        (fromNat reals (factorial k)))
    n

cosinePartialSum :
  {R : Set} ->
  CompleteOrderedField R ->
  R ->
  Nat ->
  R
cosinePartialSum reals x n =
  sumFirst reals
    (\ k ->
      multiply reals
        (alternatingSign reals k)
        (divide reals
          (power reals x (evenIndex k))
          (fromNat reals (factorial (evenIndex k)))))
    n

sinePartialSum :
  {R : Set} ->
  CompleteOrderedField R ->
  R ->
  Nat ->
  R
sinePartialSum reals x n =
  sumFirst reals
    (\ k ->
      multiply reals
        (alternatingSign reals k)
        (divide reals
          (power reals x (oddIndex k))
          (fromNat reals (factorial (oddIndex k)))))
    n

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
complement E x =
  Not (E x)

countableUnion :
  {A : Set} ->
  (Nat -> Predicate A) ->
  Predicate A
countableUnion sets x =
  Exists Nat (\ n -> sets n x)

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

record StandardRealAnalysis (R : Set) : Set1 where
  field
    algebra : CompleteOrderedField R
    squareRoot exponential cosine sine : R -> R

    square-root-nonnegative :
      (x : R) ->
      lessOrEqual algebra (zeroR algebra) x ->
      lessOrEqual algebra (zeroR algebra) (squareRoot x)
    square-root-square :
      (x : R) ->
      lessOrEqual algebra (zeroR algebra) x ->
      square algebra (squareRoot x) == x
    square-root-nonpositive :
      (x : R) ->
      lessOrEqual algebra x (zeroR algebra) ->
      squareRoot x == zeroR algebra

    exponential-series :
      (x : R) ->
      SequentialLimit algebra
        (exponentialPartialSum algebra x)
        (exponential x)
    cosine-series :
      (x : R) ->
      SequentialLimit algebra
        (cosinePartialSum algebra x)
        (cosine x)
    sine-series :
      (x : R) ->
      SequentialLimit algebra
        (sinePartialSum algebra x)
        (sine x)

    borel : SigmaAlgebra R
    borel-open-ray :
      (a : R) ->
      measurable borel (\ x -> StrictLess algebra a x)
    borel-minimal :
      (candidate : SigmaAlgebra R) ->
      ((a : R) ->
        measurable candidate (\ x -> StrictLess algebra a x)) ->
      (E : Predicate R) ->
      measurable borel E ->
      measurable candidate E

open StandardRealAnalysis

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

record Measure
  {A R : Set}
  (analysis : StandardRealAnalysis R)
  (events : SigmaAlgebra A) : Set1 where
  field
    mass : Predicate A -> R

    mass-congruent :
      (E F : Predicate A) ->
      ((x : A) -> Iff (E x) (F x)) ->
      mass E == mass F
    mass-empty :
      mass emptySet == zeroR (algebra analysis)
    mass-nonnegative :
      (E : Predicate A) ->
      measurable events E ->
      lessOrEqual (algebra analysis)
        (zeroR (algebra analysis))
        (mass E)
    countable-additivity :
      (sets : Nat -> Predicate A) ->
      ((n : Nat) -> measurable events (sets n)) ->
      PairwiseDisjoint sets ->
      SequentialLimit (algebra analysis)
        (\ count ->
          sumFirst (algebra analysis)
            (\ n -> mass (sets n))
            count)
        (mass (countableUnion sets))

open Measure

record Integration
  {A R : Set}
  (analysis : StandardRealAnalysis R)
  (events : SigmaAlgebra A)
  (measure : Measure analysis events) : Set1 where
  field
    integrable : (A -> R) -> Set
    integral : (A -> R) -> R
    indicator : Predicate A -> A -> R

    integrable-congruent :
      (f g : A -> R) ->
      ((x : A) -> f x == g x) ->
      Iff (integrable f) (integrable g)
    integral-congruent :
      (f g : A -> R) ->
      ((x : A) -> f x == g x) ->
      integral f == integral g

    integrable-zero :
      integrable (\ _ -> zeroR (algebra analysis))
    integral-zero :
      integral (\ _ -> zeroR (algebra analysis)) ==
      zeroR (algebra analysis)
    integrable-add :
      (f g : A -> R) ->
      integrable f ->
      integrable g ->
      integrable
        (\ x -> add (algebra analysis) (f x) (g x))
    integral-add :
      (f g : A -> R) ->
      integrable f ->
      integrable g ->
      integral
        (\ x -> add (algebra analysis) (f x) (g x)) ==
      add (algebra analysis) (integral f) (integral g)
    integrable-negate :
      (f : A -> R) ->
      integrable f ->
      integrable (\ x -> negate (algebra analysis) (f x))
    integral-negate :
      (f : A -> R) ->
      integrable f ->
      integral (\ x -> negate (algebra analysis) (f x)) ==
      negate (algebra analysis) (integral f)
    integrable-scale :
      (c : R) ->
      (f : A -> R) ->
      integrable f ->
      integrable
        (\ x -> multiply (algebra analysis) c (f x))
    integral-scale :
      (c : R) ->
      (f : A -> R) ->
      integrable f ->
      integral
        (\ x -> multiply (algebra analysis) c (f x)) ==
      multiply (algebra analysis) c (integral f)
    integrable-absolute :
      (f : A -> R) ->
      integrable f ->
      integrable
        (\ x -> absoluteValue (algebra analysis) (f x))
    integral-nonnegative :
      (f : A -> R) ->
      integrable f ->
      ((x : A) ->
        lessOrEqual (algebra analysis)
          (zeroR (algebra analysis))
          (f x)) ->
      lessOrEqual (algebra analysis)
        (zeroR (algebra analysis))
        (integral f)

    indicator-on :
      (E : Predicate A) ->
      (x : A) ->
      E x ->
      indicator E x == oneR (algebra analysis)
    indicator-off :
      (E : Predicate A) ->
      (x : A) ->
      Not (E x) ->
      indicator E x == zeroR (algebra analysis)
    indicator-integrable :
      (E : Predicate A) ->
      measurable events E ->
      integrable (indicator E)
    integral-indicator :
      (E : Predicate A) ->
      measurable events E ->
      integral (indicator E) == mass measure E

    bounded-measurable-integrable :
      (f : A -> R) ->
      MeasurableFunction events (borel analysis) f ->
      BoundedFunction (algebra analysis) f ->
      integrable f

    monotone-convergence :
      (functions : Nat -> A -> R) ->
      (limitFunction : A -> R) ->
      ((n : Nat) -> integrable (functions n)) ->
      ((n : Nat) ->
        (x : A) ->
        lessOrEqual (algebra analysis)
          (zeroR (algebra analysis))
          (functions n x)) ->
      ((n : Nat) ->
        (x : A) ->
        lessOrEqual (algebra analysis)
          (functions n x)
          (functions (suc n) x)) ->
      ((x : A) ->
        SequentialLimit (algebra analysis)
          (\ n -> functions n x)
          (limitFunction x)) ->
      (limitIntegral : R) ->
      SequentialLimit (algebra analysis)
        (\ n -> integral (functions n))
        limitIntegral ->
      Both
        (integrable limitFunction)
        (integral limitFunction == limitIntegral)

open Integration

record IntegratedMeasure
  {A R : Set}
  (analysis : StandardRealAnalysis R)
  (events : SigmaAlgebra A) : Set1 where
  field
    measure : Measure analysis events
    integration : Integration analysis events measure

open IntegratedMeasure

record ProbabilitySpace
  {A R : Set}
  (analysis : StandardRealAnalysis R)
  (events : SigmaAlgebra A) : Set1 where
  field
    integratedMeasure : IntegratedMeasure analysis events
    total-mass-one :
      mass (measure integratedMeasure) wholeSet ==
      oneR (algebra analysis)

open ProbabilitySpace

spaceMeasure :
  {A R : Set}
  {analysis : StandardRealAnalysis R}
  {events : SigmaAlgebra A} ->
  ProbabilitySpace analysis events ->
  Measure analysis events
spaceMeasure space =
  measure (integratedMeasure space)

spaceIntegration :
  {A R : Set}
  {analysis : StandardRealAnalysis R}
  {events : SigmaAlgebra A} ->
  (space : ProbabilitySpace analysis events) ->
  Integration analysis events (spaceMeasure space)
spaceIntegration space =
  integration (integratedMeasure space)

probabilityOf :
  {A R : Set}
  {analysis : StandardRealAnalysis R}
  {events : SigmaAlgebra A} ->
  ProbabilitySpace analysis events ->
  Predicate A ->
  R
probabilityOf space E =
  mass (spaceMeasure space) E

IsIntegrable :
  {A R : Set}
  {analysis : StandardRealAnalysis R}
  {events : SigmaAlgebra A} ->
  ProbabilitySpace analysis events ->
  (A -> R) ->
  Set
IsIntegrable space f =
  integrable (spaceIntegration space) f

expectation :
  {A R : Set}
  {analysis : StandardRealAnalysis R}
  {events : SigmaAlgebra A} ->
  ProbabilitySpace analysis events ->
  (A -> R) ->
  R
expectation space f =
  integral (spaceIntegration space) f

variance :
  {A R : Set}
  {analysis : StandardRealAnalysis R}
  {events : SigmaAlgebra A} ->
  ProbabilitySpace analysis events ->
  (A -> R) ->
  R
variance {analysis = analysis} space f =
  expectation space
    (\ x ->
      square (algebra analysis)
        (subtract (algebra analysis) (f x) (expectation space f)))

SquareIntegrable :
  {A R : Set}
  {analysis : StandardRealAnalysis R}
  {events : SigmaAlgebra A} ->
  ProbabilitySpace analysis events ->
  (A -> R) ->
  Set
SquareIntegrable {analysis = analysis} space f =
  IsIntegrable space
    (\ x -> square (algebra analysis) (f x))

record StandardProbabilityTheory (R : Set) : Set1 where
  field
    analysis : StandardRealAnalysis R

open StandardProbabilityTheory

realAlgebra :
  {R : Set} ->
  StandardProbabilityTheory R ->
  CompleteOrderedField R
realAlgebra theory =
  algebra (analysis theory)

realBorel :
  {R : Set} ->
  (theory : StandardProbabilityTheory R) ->
  SigmaAlgebra R
realBorel theory =
  borel (analysis theory)

finiteIntersection :
  {R A : Set} ->
  (Nat -> A -> R) ->
  (Nat -> Predicate R) ->
  List Nat ->
  Predicate A
finiteIntersection X sets empty _ =
  Top
finiteIntersection X sets (cons i indices) x =
  Both
    (sets i (X i x))
    (finiteIntersection X sets indices x)

finiteProbabilityProduct :
  {R A : Set}
  {analysis : StandardRealAnalysis R}
  {events : SigmaAlgebra A} ->
  ProbabilitySpace analysis events ->
  (Nat -> A -> R) ->
  (Nat -> Predicate R) ->
  List Nat ->
  R
finiteProbabilityProduct {analysis = analysis} space X sets empty =
  oneR (algebra analysis)
finiteProbabilityProduct {analysis = analysis} space X sets
  (cons i indices) =
  multiply (algebra analysis)
    (probabilityOf space (\ x -> sets i (X i x)))
    (finiteProbabilityProduct space X sets indices)

record IndependentVariables
  {R A : Set}
  (theory : StandardProbabilityTheory R)
  (events : SigmaAlgebra A)
  (space : ProbabilitySpace (analysis theory) events)
  (X : Nat -> A -> R) : Set1 where
  field
    measurable-variable :
      (n : Nat) ->
      MeasurableFunction events (realBorel theory) (X n)
    independent-pairs :
      (i j : Nat) ->
      i != j ->
      (E F : Predicate R) ->
      measurable (realBorel theory) E ->
      measurable (realBorel theory) F ->
      probabilityOf space
        (\ x -> Both (E (X i x)) (F (X j x))) ==
      multiply (realAlgebra theory)
        (probabilityOf space (preimage (X i) E))
        (probabilityOf space (preimage (X j) F))

IdenticallyDistributed :
  {R A : Set} ->
  (theory : StandardProbabilityTheory R) ->
  (events : SigmaAlgebra A) ->
  ProbabilitySpace (analysis theory) events ->
  (Nat -> A -> R) ->
  Set1
IdenticallyDistributed theory events space X =
  (n : Nat) ->
  (E : Predicate _) ->
  measurable (realBorel theory) E ->
  probabilityOf space (preimage (X n) E) ==
  probabilityOf space (preimage (X zero) E)

partialSum :
  {R A : Set} ->
  CompleteOrderedField R ->
  (Nat -> A -> R) ->
  Nat ->
  A ->
  R
partialSum reals X n x =
  sumFirst reals (\ i -> X i x) n

sampleAverage :
  {R A : Set} ->
  CompleteOrderedField R ->
  (Nat -> A -> R) ->
  Nat ->
  A ->
  R
sampleAverage reals X n x =
  divide reals
    (partialSum reals X n x)
    (fromNat reals n)

record AlmostSure
  {R A : Set}
  {analysis : StandardRealAnalysis R}
  {events : SigmaAlgebra A}
  (space : ProbabilitySpace analysis events)
  (property : Predicate A) : Set1 where
  field
    full-measure-event :
      Predicate A
    full-measure-event-measurable :
      measurable events full-measure-event
    full-measure-event-probability :
      probabilityOf space full-measure-event ==
      oneR (algebra analysis)
    property-on-full-measure-event :
      (x : A) ->
      full-measure-event x ->
      property x

strong-law-of-large-numbers : Set1
strong-law-of-large-numbers =
  (R A : Set) ->
  (theory : StandardProbabilityTheory R) ->
  (events : SigmaAlgebra A) ->
  (space : ProbabilitySpace (analysis theory) events) ->
  (X : Nat -> A -> R) ->
  IndependentVariables theory events space X ->
  IdenticallyDistributed theory events space X ->
  IsIntegrable space (X zero) ->
  AlmostSure space
    (\ x ->
      SequentialLimit (realAlgebra theory)
        (\ n -> sampleAverage (realAlgebra theory) X n x)
        (expectation space (X zero)))
