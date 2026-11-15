-- Statement-only formalization of PutnamBench corpus artifact putnam_2024_b4
-- (putnambench__agda__putnam_2024_b4): the normalized expected position of
-- the independently driven uniform integer walk converges to
-- (1 - exp(-2)) / 2. This file contains no proof.

{-# OPTIONS --safe #-}

module Main where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality renaming (_≡_ to _==_)
open import Agda.Builtin.Int using (Int; pos; negsuc)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)

infix 4 _!=_ _<=N_
infixr 3 _and_
infixr 2 _or_

data Bottom : Set where

record Top : Set where
  constructor top

Not : Set -> Set
Not A =
  A -> Bottom

_!=_ : {A : Set} -> A -> A -> Set
x != y =
  Not (x == y)

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

oneN : Nat
oneN =
  suc zero

twoN : Nat
twoN =
  suc oneN

Positive : Nat -> Set
Positive n =
  oneN <=N n

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
divide reals numerator denominator =
  multiply reals numerator (inverse reals denominator)

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

factorial : Nat -> Nat
factorial zero =
  oneN
factorial (suc n) =
  suc n * factorial n

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

ExponentialValue :
  {R : Set} ->
  CompleteOrderedRealField R ->
  R ->
  R ->
  Set
ExponentialValue reals x value =
  SeriesHasSum reals
    (exponentialTerm reals x)
    value

record StandardRealAnalysis
  {R : Set}
  (reals : CompleteOrderedRealField R) :
  Set1 where

  field
    exponential : R -> R
    exponential-series :
      (x : R) ->
      ExponentialValue reals x (exponential x)

open StandardRealAnalysis

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
preimage function event x =
  event (function x)

MeasurableFunction :
  {A B : Set} ->
  SigmaAlgebra A ->
  SigmaAlgebra B ->
  (A -> B) ->
  Set1
MeasurableFunction source target function =
  (event : Predicate _) ->
  measurable target event ->
  measurable source (preimage function event)

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
BoundedFunction {A} {R} reals function =
  Exists R
    (\ bound ->
      lessOrEqual reals (zeroR reals) bound
      and
      ((x : A) ->
        lessOrEqual reals
          (absoluteValue reals (function x))
          bound))

PointwiseNonnegative :
  {A R : Set} ->
  CompleteOrderedRealField R ->
  (A -> R) ->
  Set
PointwiseNonnegative {A} reals function =
  (x : A) ->
  lessOrEqual reals (zeroR reals) (function x)

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
NullSet {reals = reals} measure event =
  mass measure event == zeroR reals

AlmostEverywhere :
  {A R : Set}
  {reals : CompleteOrderedRealField R}
  {events : SigmaAlgebra A} ->
  Measure reals events ->
  Predicate A ->
  Set
AlmostEverywhere measure property =
  NullSet measure (\ x -> Not (property x))

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
      suc i <=N count ->
      measurable events (pieces i)
    pieces-disjoint :
      (i j : Nat) ->
      suc i <=N count ->
      suc j <=N count ->
      i != j ->
      (x : A) ->
      pieces i x ->
      pieces j x ->
      Bottom
    pieces-cover :
      (x : A) ->
      Exists Nat
        (\ i ->
          suc i <=N count
          and
          pieces i x)
    represented-on-pieces :
      (i : Nat) ->
      suc i <=N count ->
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
probabilityOf space event =
  mass (measure space) event

expectation :
  {A R : Set}
  {reals : CompleteOrderedRealField R}
  {theory : StandardProbabilityTheory R reals}
  {events : SigmaAlgebra A} ->
  ProbabilitySpace reals theory events ->
  (A -> R) ->
  R
expectation space randomVariable =
  integral (integration space) randomVariable

negative : Nat -> Int
negative zero =
  pos zero
negative (suc n) =
  negsuc n

negateInt : Int -> Int
negateInt (pos n) =
  negative n
negateInt (negsuc n) =
  pos (suc n)

differenceNat : Nat -> Nat -> Int
differenceNat zero zero =
  pos zero
differenceNat (suc m) zero =
  pos (suc m)
differenceNat zero (suc n) =
  negsuc n
differenceNat (suc m) (suc n) =
  differenceNat m n

addInt : Int -> Int -> Int
addInt (pos m) (pos n) =
  pos (m + n)
addInt (pos m) (negsuc n) =
  differenceNat m (suc n)
addInt (negsuc m) (pos n) =
  differenceNat n (suc m)
addInt (negsuc m) (negsuc n) =
  negsuc (suc (m + n))

subtractInt : Int -> Int -> Int
subtractInt x y =
  addInt x (negateInt y)

zeroZ : Int
zeroZ =
  pos zero

oneZ : Int
oneZ =
  pos oneN

natEqual : Nat -> Nat -> Bool
natEqual zero zero =
  true
natEqual zero (suc n) =
  false
natEqual (suc m) zero =
  false
natEqual (suc m) (suc n) =
  natEqual m n

natLess : Nat -> Nat -> Bool
natLess zero zero =
  false
natLess zero (suc n) =
  true
natLess (suc m) zero =
  false
natLess (suc m) (suc n) =
  natLess m n

natLessOrEqual : Nat -> Nat -> Bool
natLessOrEqual zero n =
  true
natLessOrEqual (suc m) zero =
  false
natLessOrEqual (suc m) (suc n) =
  natLessOrEqual m n

intEqual : Int -> Int -> Bool
intEqual (pos m) (pos n) =
  natEqual m n
intEqual (pos m) (negsuc n) =
  false
intEqual (negsuc m) (pos n) =
  false
intEqual (negsuc m) (negsuc n) =
  natEqual m n

intLess : Int -> Int -> Bool
intLess (pos m) (pos n) =
  natLess m n
intLess (pos m) (negsuc n) =
  false
intLess (negsuc m) (pos n) =
  true
intLess (negsuc m) (negsuc n) =
  natLess n m

walkStep : Int -> Int -> Int
walkStep draw state with intLess state draw
... | true =
  addInt state oneZ
... | false with intEqual draw state
...   | true =
  state
...   | false =
  subtractInt state oneZ

fromInt :
  {R : Set} ->
  CompleteOrderedRealField R ->
  Int ->
  R
fromInt reals (pos n) =
  fromNat reals n
fromInt reals (negsuc n) =
  negate reals (fromNat reals (suc n))

inOneThrough : Nat -> Int -> Bool
inOneThrough n (pos zero) =
  false
inOneThrough n (pos (suc k)) =
  natLessOrEqual (suc k) n
inOneThrough n (negsuc k) =
  false

uniformPointMass :
  {R : Set} ->
  CompleteOrderedRealField R ->
  Nat ->
  Int ->
  R
uniformPointMass reals n z with inOneThrough n z
... | true =
  divide reals
    (oneR reals)
    (fromNat reals n)
... | false =
  zeroR reals

MeasurableIntFunction :
  {A : Set} ->
  SigmaAlgebra A ->
  (A -> Int) ->
  Set
MeasurableIntFunction events function =
  (z : Int) ->
  measurable events
    (\ outcome -> function outcome == z)

UniformOnOneThrough :
  {A R : Set}
  {reals : CompleteOrderedRealField R}
  {theory : StandardProbabilityTheory R reals}
  {events : SigmaAlgebra A} ->
  ProbabilitySpace reals theory events ->
  Nat ->
  (A -> Int) ->
  Set
UniformOnOneThrough
  {reals = reals} {events = events}
  space n randomVariable =
  MeasurableIntFunction events randomVariable
  and
  ((z : Int) ->
    probabilityOf space
      (\ outcome -> randomVariable outcome == z)
    ==
    uniformPointMass reals n z)

record Index : Set where
  constructor index
  field
    row    : Nat
    column : Nat

open Index

indexed :
  {A : Set} ->
  (Nat -> Nat -> A) ->
  Index ->
  A
indexed family i =
  family (row i) (column i)

finiteIntersection :
  {A I : Set} ->
  (I -> A -> Int) ->
  (I -> Predicate Int) ->
  List I ->
  Predicate A
finiteIntersection X targets empty _ =
  Top
finiteIntersection X targets (cons i indices) outcome =
  targets i (X i outcome)
  and
  finiteIntersection X targets indices outcome

finiteProbabilityProduct :
  {A I R : Set}
  {reals : CompleteOrderedRealField R}
  {theory : StandardProbabilityTheory R reals}
  {events : SigmaAlgebra A} ->
  ProbabilitySpace reals theory events ->
  (I -> A -> Int) ->
  (I -> Predicate Int) ->
  List I ->
  R
finiteProbabilityProduct {reals = reals} space X targets empty =
  oneR reals
finiteProbabilityProduct {reals = reals} space X targets
  (cons i indices) =
  multiply reals
    (probabilityOf space (preimage (X i) (targets i)))
    (finiteProbabilityProduct space X targets indices)

record IndependentIntRandomVariables
  {A I R : Set}
  {reals : CompleteOrderedRealField R}
  {theory : StandardProbabilityTheory R reals}
  {events : SigmaAlgebra A}
  (space : ProbabilitySpace reals theory events)
  (X : I -> A -> Int) :
  Set1 where

  field
    coordinates-measurable :
      (i : I) ->
      MeasurableIntFunction events (X i)
    independent-events :
      (indices : List I) ->
      NoDuplicates indices ->
      (targets : I -> Predicate Int) ->
      probabilityOf space
        (finiteIntersection X targets indices)
      ==
      finiteProbabilityProduct space X targets indices

normalizedExpectation :
  {A R : Set}
  {reals : CompleteOrderedRealField R}
  {theory : StandardProbabilityTheory R reals}
  {events : SigmaAlgebra A} ->
  ProbabilitySpace reals theory events ->
  (Nat -> Nat -> A -> Int) ->
  Nat ->
  R
normalizedExpectation {reals = reals} space a n =
  divide reals
    (expectation space
      (\ outcome -> fromInt reals (a n n outcome)))
    (fromNat reals n)

putnam-2024-b4-solution :
  {R : Set} ->
  (reals : CompleteOrderedRealField R) ->
  StandardRealAnalysis reals ->
  R
putnam-2024-b4-solution reals analysis =
  divide reals
    (subtract reals
      (oneR reals)
      (exponential analysis
        (negate reals (fromNat reals twoN))))
    (fromNat reals twoN)

putnam-2024-b4 : Set1
putnam-2024-b4 =
  (R : Set) ->
  (reals : CompleteOrderedRealField R) ->
  (analysis : StandardRealAnalysis reals) ->
  (Omega : Set) ->
  (theory : StandardProbabilityTheory R reals) ->
  (events : SigmaAlgebra Omega) ->
  (space : ProbabilitySpace reals theory events) ->
  (m a : Nat -> Nat -> Omega -> Int) ->
  ((n : Nat) ->
    Positive n ->
    (outcome : Omega) ->
    a n zero outcome == oneZ) ->
  ((n k : Nat) ->
    Positive n ->
    UniformOnOneThrough space n (m n k)) ->
  ((n k : Nat) ->
    (outcome : Omega) ->
    Positive n ->
    a n (suc k) outcome ==
      walkStep (m n k outcome) (a n k outcome)) ->
  IndependentIntRandomVariables space (indexed m) ->
  ConvergesTo reals
    (normalizedExpectation space a)
    (putnam-2024-b4-solution reals analysis)
