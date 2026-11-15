-- Statement-only formalization of PutnamBench corpus artifact putnam_1962_a2:
-- classification of nonnegative real functions whose interval average from
-- zero is the geometric mean of the endpoint values.
-- This file contains no proof.

{-# OPTIONS --safe #-}

module Main where

open import Agda.Builtin.Equality renaming (_≡_ to _==_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)

infix 4 _!=_ _<=N_
infixr 3 _and_
infixr 2 _or_

data Bottom : Set where

Not : Set -> Set
Not A = A -> Bottom

Not1 : Set1 -> Set1
Not1 A = A -> Bottom

_!=_ : {A : Set} -> A -> A -> Set
x != y = Not (x == y)

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

record Exists1 (A : Set) (P : A -> Set1) : Set1 where
  constructor witness1
  field
    value1    : A
    property1 : P value1

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

record CompleteOrderedField (R : Set) : Set1 where
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
      (n : Nat) -> fromNat (suc n) == add (fromNat n) oneR
    fromNat-addition :
      (m n : Nat) ->
      fromNat (m + n) == add (fromNat m) (fromNat n)
    fromNat-injective :
      (m n : Nat) -> fromNat m == fromNat n -> m == n

    archimedean :
      (x : R) ->
      Exists Nat (\ n -> lessOrEqual x (fromNat n))
    least-upper-bound :
      (P : Predicate R) ->
      Exists R P ->
      Exists R
        (\ upper ->
          (x : R) -> P x -> lessOrEqual x upper) ->
      Exists R
        (\ supremum ->
          ((x : R) -> P x -> lessOrEqual x supremum)
          and
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
  multiply reals x (inverse reals y)

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
  lessOrEqual reals x y and x != y

CloseTo :
  {R : Set} ->
  CompleteOrderedField R ->
  R ->
  R ->
  R ->
  Set
CloseTo reals center radius x =
  StrictLess reals
    (subtract reals center radius)
    x
  and
  StrictLess reals
    x
    (add reals center radius)

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
      CloseTo reals limit epsilon (sequence n))

sumFirst :
  {R : Set} ->
  CompleteOrderedField R ->
  (Nat -> R) ->
  Nat ->
  R
sumFirst reals terms zero =
  zeroR reals
sumFirst reals terms (suc n) =
  add reals
    (sumFirst reals terms n)
    (terms n)

record StandardRealAnalysis (R : Set) : Set1 where
  field
    algebra : CompleteOrderedField R
    squareRoot : R -> R
    positivePart : R -> R

    square-root-nonnegative :
      (x : R) ->
      lessOrEqual algebra (zeroR algebra) (squareRoot x)
    square-root-square :
      (x : R) ->
      lessOrEqual algebra (zeroR algebra) x ->
      square algebra (squareRoot x) == x
    square-root-nonpositive :
      (x : R) ->
      lessOrEqual algebra x (zeroR algebra) ->
      squareRoot x == zeroR algebra
    square-root-unique :
      (x y : R) ->
      lessOrEqual algebra (zeroR algebra) y ->
      square algebra y == x ->
      squareRoot x == y

    positive-part-nonnegative :
      (x : R) ->
      lessOrEqual algebra (zeroR algebra) (positivePart x)
    positive-part-of-nonnegative :
      (x : R) ->
      lessOrEqual algebra (zeroR algebra) x ->
      positivePart x == x
    positive-part-of-nonpositive :
      (x : R) ->
      lessOrEqual algebra x (zeroR algebra) ->
      positivePart x == zeroR algebra

open StandardRealAnalysis

HalfOpen :
  {R : Set} ->
  CompleteOrderedField R ->
  R ->
  R ->
  Predicate R
HalfOpen reals lower upper x =
  lessOrEqual reals lower x
  and
  StrictLess reals x upper

data BorelCode
  {R : Set}
  (reals : CompleteOrderedField R) : Set where
  emptyB          : BorelCode reals
  openRayB        : R -> BorelCode reals
  complementB     : BorelCode reals -> BorelCode reals
  countableUnionB : (Nat -> BorelCode reals) -> BorelCode reals

decodeBorel :
  {R : Set} ->
  (reals : CompleteOrderedField R) ->
  BorelCode reals ->
  Predicate R
decodeBorel reals emptyB =
  emptySet
decodeBorel reals (openRayB endpoint) x =
  StrictLess reals endpoint x
decodeBorel reals (complementB code) =
  complement (decodeBorel reals code)
decodeBorel reals (countableUnionB codes) =
  countableUnion (\ n -> decodeBorel reals (codes n))

LocallyNull :
  {R : Set} ->
  (reals : CompleteOrderedField R) ->
  (R -> R -> Predicate R -> R) ->
  Predicate R ->
  Set
LocallyNull reals intervalMeasure N =
  (lower upper : _) ->
  lessOrEqual reals lower upper ->
  intervalMeasure lower upper N == zeroR reals

record CompletedBorelWitness
  {R : Set}
  (reals : CompleteOrderedField R)
  (intervalMeasure : R -> R -> Predicate R -> R)
  (S : Predicate R) : Set where
  field
    representative : BorelCode reals
    nullEnvelope : BorelCode reals
    null-envelope-locally-null :
      LocallyNull reals intervalMeasure
        (decodeBorel reals nullEnvelope)
    agrees-off-null :
      (x : R) ->
      Not (decodeBorel reals nullEnvelope x) ->
      Iff (S x) (decodeBorel reals representative x)

open CompletedBorelWitness

record BorelIntervalMeasureLaws
  {R : Set}
  (reals : CompleteOrderedField R)
  (intervalMeasure : R -> R -> Predicate R -> R) : Set1 where
  field
    borel-measure-congruent :
      (lower upper : R) ->
      (S T : Predicate R) ->
      ((x : R) -> Iff (S x) (T x)) ->
      intervalMeasure lower upper S ==
      intervalMeasure lower upper T
    borel-measure-empty :
      (lower upper : R) ->
      intervalMeasure lower upper emptySet == zeroR reals
    borel-measure-nonnegative :
      (lower upper : R) ->
      lessOrEqual reals lower upper ->
      (code : BorelCode reals) ->
      lessOrEqual reals
        (zeroR reals)
        (intervalMeasure lower upper (decodeBorel reals code))
    borel-measure-restricted :
      (lower upper : R) ->
      (S : Predicate R) ->
      intervalMeasure lower upper S ==
      intervalMeasure lower upper
        (\ x -> S x and HalfOpen reals lower upper x)
    borel-measure-half-open :
      (lower upper start endpoint : R) ->
      lessOrEqual reals lower start ->
      lessOrEqual reals start endpoint ->
      lessOrEqual reals endpoint upper ->
      intervalMeasure lower upper
        (HalfOpen reals start endpoint) ==
      subtract reals endpoint start
    borel-measure-countable-additivity :
      (lower upper : R) ->
      lessOrEqual reals lower upper ->
      (codes : Nat -> BorelCode reals) ->
      PairwiseDisjoint
        (\ n -> decodeBorel reals (codes n)) ->
      SequentialLimit reals
        (\ count ->
          sumFirst reals
            (\ n ->
              intervalMeasure lower upper
                (decodeBorel reals (codes n)))
            count)
        (intervalMeasure lower upper
          (decodeBorel reals (countableUnionB codes)))

record RestrictedLebesgueMeasure
  {R : Set}
  (analysis : StandardRealAnalysis R) : Set1 where
  private
    reals = algebra analysis

  field
    intervalMeasure : R -> R -> Predicate R -> R
    measurable : Predicate R -> Set
    measureFromZero : R -> Predicate R -> R

    measure-from-zero :
      (upper : R) ->
      (S : Predicate R) ->
      measureFromZero upper S ==
      intervalMeasure (zeroR reals) upper S
    measurable-exact :
      (S : Predicate R) ->
      Iff
        (measurable S)
        (CompletedBorelWitness reals intervalMeasure S)
    borel-measure-laws :
      BorelIntervalMeasureLaws reals intervalMeasure
    borel-measure-unique :
      (candidate : R -> R -> Predicate R -> R) ->
      BorelIntervalMeasureLaws reals candidate ->
      (lower upper : R) ->
      lessOrEqual reals lower upper ->
      (code : BorelCode reals) ->
      candidate lower upper (decodeBorel reals code) ==
      intervalMeasure lower upper (decodeBorel reals code)
    interval-measure-completion :
      (lower upper : R) ->
      lessOrEqual reals lower upper ->
      (S : Predicate R) ->
      (completion :
        CompletedBorelWitness reals intervalMeasure S) ->
      intervalMeasure lower upper S ==
      intervalMeasure lower upper
        (decodeBorel reals (representative completion))

    measurable-empty :
      measurable emptySet
    measurable-complement :
      (S : Predicate R) ->
      measurable S ->
      measurable (complement S)
    measurable-countable-union :
      (sets : Nat -> Predicate R) ->
      ((n : Nat) -> measurable (sets n)) ->
      measurable (countableUnion sets)
    measurable-congruent :
      (S T : Predicate R) ->
      ((x : R) -> Iff (S x) (T x)) ->
      measurable S ->
      measurable T
    measurable-half-open :
      (lower upper : R) ->
      measurable (HalfOpen reals lower upper)
    measurable-open-ray :
      (endpoint : R) ->
      measurable (\ x -> StrictLess reals endpoint x)
    complete-on-null-sets :
      (upper : R) ->
      lessOrEqual reals (zeroR reals) upper ->
      (N S : Predicate R) ->
      measurable N ->
      measureFromZero upper N == zeroR reals ->
      Subset S N ->
      measurable
        (\ x ->
          S x
          and
          HalfOpen reals (zeroR reals) upper x)

    measure-congruent :
      (upper : R) ->
      (S T : Predicate R) ->
      ((x : R) -> Iff (S x) (T x)) ->
      measureFromZero upper S == measureFromZero upper T
    measure-empty :
      (upper : R) ->
      measureFromZero upper emptySet == zeroR reals
    measure-nonnegative :
      (upper : R) ->
      lessOrEqual reals (zeroR reals) upper ->
      (S : Predicate R) ->
      measurable S ->
      lessOrEqual reals
        (zeroR reals)
        (measureFromZero upper S)
    measure-restricted :
      (upper : R) ->
      (S : Predicate R) ->
      measureFromZero upper S ==
      measureFromZero upper
        (\ x -> S x and HalfOpen reals (zeroR reals) upper x)
    measure-half-open :
      (upper lower endpoint : R) ->
      lessOrEqual reals (zeroR reals) lower ->
      lessOrEqual reals lower endpoint ->
      lessOrEqual reals endpoint upper ->
      measureFromZero upper (HalfOpen reals lower endpoint) ==
      subtract reals endpoint lower
    measure-countable-additivity :
      (upper : R) ->
      lessOrEqual reals (zeroR reals) upper ->
      (sets : Nat -> Predicate R) ->
      ((n : Nat) -> measurable (sets n)) ->
      PairwiseDisjoint sets ->
      SequentialLimit reals
        (\ count ->
          sumFirst reals
            (\ n -> measureFromZero upper (sets n))
            count)
        (measureFromZero upper (countableUnion sets))

open RestrictedLebesgueMeasure

record NonnegativeSimpleBelow
  {R : Set}
  (analysis : StandardRealAnalysis R)
  (lebesgue : RestrictedLebesgueMeasure analysis)
  (upper : R)
  (function : R -> R) : Set1 where
  private
    reals = algebra analysis

  field
    cutoff : Nat
    values : Nat -> R
    pieces : Nat -> Predicate R

    values-nonnegative :
      (i : Nat) ->
      i <=N cutoff ->
      lessOrEqual reals (zeroR reals) (values i)
    pieces-measurable :
      (i : Nat) ->
      i <=N cutoff ->
      measurable lebesgue (pieces i)
    pieces-disjoint :
      (i j : Nat) ->
      i <=N cutoff ->
      j <=N cutoff ->
      i != j ->
      (x : R) ->
      pieces i x ->
      pieces j x ->
      Bottom
    pieces-inside-interval :
      (i : Nat) ->
      i <=N cutoff ->
      Subset
        (pieces i)
        (HalfOpen reals (zeroR reals) upper)
    below-function :
      (i : Nat) ->
      i <=N cutoff ->
      (x : R) ->
      pieces i x ->
      lessOrEqual reals (values i) (function x)

open NonnegativeSimpleBelow

simpleIntegral :
  {R : Set} ->
  (analysis : StandardRealAnalysis R) ->
  (lebesgue : RestrictedLebesgueMeasure analysis) ->
  {upper : R} ->
  {function : R -> R} ->
  NonnegativeSimpleBelow analysis lebesgue upper function ->
  R
simpleIntegral analysis lebesgue {upper = upper} simple =
  sumFirst (algebra analysis)
    (\ i ->
      multiply (algebra analysis)
        (values simple i)
        (measureFromZero lebesgue
          upper
          (pieces simple i)))
    (suc (cutoff simple))

data ExtendedNonnegative
  {R : Set}
  (reals : CompleteOrderedField R) : Set where
  finiteE   : R -> ExtendedNonnegative reals
  infinityE : ExtendedNonnegative reals

NonnegativeExtended :
  {R : Set} ->
  (reals : CompleteOrderedField R) ->
  ExtendedNonnegative reals ->
  Set
NonnegativeExtended reals (finiteE value) =
  lessOrEqual reals (zeroR reals) value
NonnegativeExtended reals infinityE =
  Top

LessOrEqualE :
  {R : Set} ->
  (reals : CompleteOrderedField R) ->
  ExtendedNonnegative reals ->
  ExtendedNonnegative reals ->
  Set
LessOrEqualE reals (finiteE x) (finiteE y) =
  lessOrEqual reals x y
LessOrEqualE reals (finiteE x) infinityE =
  Top
LessOrEqualE reals infinityE (finiteE y) =
  Bottom
LessOrEqualE reals infinityE infinityE =
  Top

RealBelowE :
  {R : Set} ->
  (reals : CompleteOrderedField R) ->
  R ->
  ExtendedNonnegative reals ->
  Set
RealBelowE reals x (finiteE y) =
  lessOrEqual reals x y
RealBelowE reals x infinityE =
  Top

record LowerLebesgueIntegralValue
  {R : Set}
  (analysis : StandardRealAnalysis R)
  (lebesgue : RestrictedLebesgueMeasure analysis)
  (upper : R)
  (function : R -> R)
  (value : ExtendedNonnegative (algebra analysis)) : Set1 where
  private
    reals = algebra analysis

  field
    value-nonnegative :
      NonnegativeExtended reals value
    simple-integrals-below :
      (simple :
        NonnegativeSimpleBelow
          analysis lebesgue upper function) ->
      RealBelowE reals
        (simpleIntegral analysis lebesgue simple)
        value
    least-upper-bound :
      (bound : ExtendedNonnegative reals) ->
      ((simple :
          NonnegativeSimpleBelow
            analysis lebesgue upper function) ->
        RealBelowE reals
          (simpleIntegral analysis lebesgue simple)
          bound) ->
      LessOrEqualE reals value bound

positivePartFunction :
  {R : Set} ->
  StandardRealAnalysis R ->
  (R -> R) ->
  R ->
  R
positivePartFunction analysis function x =
  positivePart analysis (function x)

negativePartFunction :
  {R : Set} ->
  StandardRealAnalysis R ->
  (R -> R) ->
  R ->
  R
negativePartFunction analysis function x =
  positivePart analysis
    (negate (algebra analysis) (function x))

MeasurableOnFromZero :
  {R : Set} ->
  (analysis : StandardRealAnalysis R) ->
  RestrictedLebesgueMeasure analysis ->
  R ->
  (R -> R) ->
  Set
MeasurableOnFromZero analysis lebesgue upper function =
  (threshold : _) ->
  measurable lebesgue
    (\ x ->
      HalfOpen
        (algebra analysis)
        (zeroR (algebra analysis))
        upper
        x
      and
      StrictLess
        (algebra analysis)
        threshold
        (function x))

record FiniteLowerIntegralValue
  {R : Set}
  (analysis : StandardRealAnalysis R)
  (lowerIntegral :
    (R -> R) ->
    R ->
    ExtendedNonnegative (algebra analysis))
  (upper : R)
  (function : R -> R)
  (value : R) : Set where
  private
    reals = algebra analysis

  field
    finite-value-nonnegative :
      lessOrEqual reals (zeroR reals) value
    finite-value-equation :
      lowerIntegral function upper == finiteE value

record IntegrableIntervalValue
  {R : Set}
  (analysis : StandardRealAnalysis R)
  (lebesgue : RestrictedLebesgueMeasure analysis)
  (lowerIntegral :
    (R -> R) ->
    R ->
    ExtendedNonnegative (algebra analysis))
  (upper : R)
  (function : R -> R)
  (value : R) : Set1 where
  private
    reals = algebra analysis

  field
    measurable-on-interval :
      MeasurableOnFromZero analysis lebesgue upper function
    positive-integral negative-integral : R
    positive-part-finite :
      FiniteLowerIntegralValue
        analysis lowerIntegral upper
        (positivePartFunction analysis function)
        positive-integral
    negative-part-finite :
      FiniteLowerIntegralValue
        analysis lowerIntegral upper
        (negativePartFunction analysis function)
        negative-integral
    signed-value :
      value ==
      subtract reals positive-integral negative-integral

data TotalizedLebesgueIntegralValue
  {R : Set}
  (analysis : StandardRealAnalysis R)
  (lebesgue : RestrictedLebesgueMeasure analysis)
  (lowerIntegral :
    (R -> R) ->
    R ->
    ExtendedNonnegative (algebra analysis))
  (upper : R)
  (function : R -> R)
  (value : R) : Set1 where
  integrable-value :
    IntegrableIntervalValue
      analysis lebesgue lowerIntegral upper function value ->
    TotalizedLebesgueIntegralValue
      analysis lebesgue lowerIntegral upper function value
  nonintegrable-value :
    Not1
      (Exists1 R
        (\ candidate ->
          IntegrableIntervalValue
            analysis lebesgue lowerIntegral
            upper function candidate)) ->
    value == zeroR (algebra analysis) ->
    TotalizedLebesgueIntegralValue
      analysis lebesgue lowerIntegral upper function value

-- In the standard real model, these fields are the completed-Borel Lebesgue
-- lower integral and its usual real-valued totalization, which is zero when
-- the function is not integrable.
record LebesgueIntervalIntegration
  {R : Set}
  (analysis : StandardRealAnalysis R)
  (lebesgue : RestrictedLebesgueMeasure analysis) : Set1 where
  private
    reals = algebra analysis

  field
    lowerIntegral :
      (R -> R) ->
      R ->
      ExtendedNonnegative reals
    integralFromZero : (R -> R) -> R -> R
    lower-integral-definition :
      (function : R -> R) ->
      ((x : R) ->
        lessOrEqual reals (zeroR reals) (function x)) ->
      (upper : R) ->
      lessOrEqual reals (zeroR reals) upper ->
      LowerLebesgueIntegralValue
        analysis lebesgue upper function
        (lowerIntegral function upper)
    lower-integral-unique :
      (function : R -> R) ->
      ((x : R) ->
        lessOrEqual reals (zeroR reals) (function x)) ->
      (upper : R) ->
      lessOrEqual reals (zeroR reals) upper ->
      (value : ExtendedNonnegative reals) ->
      LowerLebesgueIntegralValue
        analysis lebesgue upper function value ->
      lowerIntegral function upper == value
    totalized-integral-definition :
      (function : R -> R) ->
      (upper : R) ->
      lessOrEqual reals (zeroR reals) upper ->
      TotalizedLebesgueIntegralValue
        analysis lebesgue lowerIntegral upper function
        (integralFromZero function upper)
    totalized-integral-unique :
      (function : R -> R) ->
      (upper : R) ->
      lessOrEqual reals (zeroR reals) upper ->
      (value : R) ->
      TotalizedLebesgueIntegralValue
        analysis lebesgue lowerIntegral upper function value ->
      integralFromZero function upper == value

open LebesgueIntervalIntegration

module Putnam1962A2Statement
  {R : Set}
  (analysis : StandardRealAnalysis R)
  (lebesgue : RestrictedLebesgueMeasure analysis)
  (integration : LebesgueIntervalIntegration analysis lebesgue) where

  reals : CompleteOrderedField R
  reals =
    algebra analysis

  NonnegativeFunction : (R -> R) -> Set
  NonnegativeFunction f =
    (x : R) ->
    lessOrEqual reals (zeroR reals) (f x)

  InfinitePositiveInterval : Predicate R
  InfinitePositiveInterval x =
    StrictLess reals (zeroR reals) x

  FinitePositiveInterval : R -> Predicate R
  FinitePositiveInterval endpoint x =
    StrictLess reals (zeroR reals) x
    and
    StrictLess reals x endpoint

  InfiniteClosedInterval : Predicate R
  InfiniteClosedInterval x =
    lessOrEqual reals (zeroR reals) x

  FiniteHalfOpenInterval : R -> Predicate R
  FiniteHalfOpenInterval endpoint =
    HalfOpen reals (zeroR reals) endpoint

  EqOn :
    (R -> R) ->
    (R -> R) ->
    Predicate R ->
    Set
  EqOn f g domain =
    (x : R) ->
    domain x ->
    f x == g x

  IntervalCondition :
    Predicate R ->
    (R -> R) ->
    Set
  IntervalCondition domain f =
    NonnegativeFunction f
    and
    ((x : R) ->
      domain x ->
      divide reals
        (integralFromZero integration f x)
        x
      ==
      squareRoot analysis
        (multiply reals (f (zeroR reals)) (f x)))

  RationalSquareValue : R -> R -> R -> R
  RationalSquareValue a c x =
    divide reals
      a
      (square reals
        (subtract reals
          (oneR reals)
          (multiply reals c x)))

  GlobalRationalSquareFamily : (R -> R) -> Set
  GlobalRationalSquareFamily f =
    Exists R
      (\ a ->
        Exists R
          (\ c ->
            lessOrEqual reals (zeroR reals) a
            and
            ((x : R) ->
              f x ==
              RationalSquareValue a c x)))

  TruncatedRationalSquareFamily : (R -> R) -> Set
  TruncatedRationalSquareFamily f =
    Exists R
      (\ a ->
        Exists R
          (\ c ->
            lessOrEqual reals (zeroR reals) a
            and
            StrictLess reals (zeroR reals) c
            and
            ((x : R) ->
              let cutoff = divide reals (oneR reals) c
              in
              (StrictLess reals x cutoff
                and
                f x == RationalSquareValue a c x)
              or
              (lessOrEqual reals cutoff x
                and
                f x == zeroR reals))))

  PositiveRayZeroFamily : (R -> R) -> Set
  PositiveRayZeroFamily f =
    NonnegativeFunction f
    and
    ((x : R) ->
      StrictLess reals (zeroR reals) x ->
      f x == zeroR reals)

  InitialAverageZeroFamily : (R -> R) -> Set
  InitialAverageZeroFamily f =
    Exists R
      (\ endpoint ->
        StrictLess reals (zeroR reals) endpoint
        and
        f (zeroR reals) == zeroR reals
        and
        NonnegativeFunction f
        and
        ((x : R) ->
          FinitePositiveInterval endpoint x ->
          divide reals
            (integralFromZero integration f x)
            x
          ==
          zeroR reals))

  PutnamSolutionFamily : (R -> R) -> Set
  PutnamSolutionFamily f =
    GlobalRationalSquareFamily f

  proposition : Set
  proposition =
    ((f : R -> R) ->
      (IntervalCondition InfinitePositiveInterval f ->
        Exists (R -> R)
          (\ g ->
            PutnamSolutionFamily g
            and
            EqOn f g InfiniteClosedInterval))
      and
      ((endpoint : R) ->
        StrictLess reals (zeroR reals) endpoint ->
        IntervalCondition (FinitePositiveInterval endpoint) f ->
        Exists (R -> R)
          (\ g ->
            PutnamSolutionFamily g
            and
            EqOn f g (FiniteHalfOpenInterval endpoint))))
    and
    ((f : R -> R) ->
      PutnamSolutionFamily f ->
      IntervalCondition InfinitePositiveInterval f
      or
      Exists R
        (\ endpoint ->
          StrictLess reals (zeroR reals) endpoint
          and
          IntervalCondition
            (FinitePositiveInterval endpoint)
            f))

putnam-1962-a2 : Set1
putnam-1962-a2 =
  (R : Set) ->
  (analysis : StandardRealAnalysis R) ->
  (lebesgue : RestrictedLebesgueMeasure analysis) ->
  (integration : LebesgueIntervalIntegration analysis lebesgue) ->
  Putnam1962A2Statement.proposition
    analysis lebesgue integration
