-- Statement-only formalization of thousand-theorems corpus artifact Q190391,
-- "Central limit theorem": centered sums of independent identically distributed
-- square-integrable real random variables converge weakly, through their
-- pushforward laws, to the canonical centered Gaussian law of their variance.
-- This file contains no proof.

{-# OPTIONS --safe #-}

module Q190391_central_limit_theorem where

open import Agda.Builtin.Equality renaming (_≡_ to _==_)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)
open import Q1966978_levy_continuity_theorem

open CompleteOrderedField

record ExactMeasurableSpace (A : Set) : Set2 where
  field
    event :
      Predicate A ->
      Set1
    event-congruent :
      (S T : Predicate A) ->
      ((x : A) -> Iff (S x) (T x)) ->
      event S ->
      event T
    event-empty :
      event emptySet
    event-complement :
      (S : Predicate A) ->
      event S ->
      event (complement S)
    event-countable-union :
      (sets : Nat -> Predicate A) ->
      ((n : Nat) -> event (sets n)) ->
      event (countableUnion sets)

open ExactMeasurableSpace

data RealBorelEvent
  {R : Set}
  (reals : CompleteOrderedField R) :
  Predicate R -> Set1 where
  generated-open :
    {U : Predicate R} ->
    MetricOpenReal reals U ->
    RealBorelEvent reals U
  generated-empty :
    RealBorelEvent reals emptySet
  generated-complement :
    {S : Predicate R} ->
    RealBorelEvent reals S ->
    RealBorelEvent reals (complement S)
  generated-countable-union :
    (sets : Nat -> Predicate R) ->
    ((n : Nat) -> RealBorelEvent reals (sets n)) ->
    RealBorelEvent reals (countableUnion sets)
  generated-congruent :
    {S T : Predicate R} ->
    ((x : R) -> Iff (S x) (T x)) ->
    RealBorelEvent reals S ->
    RealBorelEvent reals T

realBorelEvents :
  {R : Set} ->
  CompleteOrderedField R ->
  ExactMeasurableSpace R
realBorelEvents reals =
  record
    { event = RealBorelEvent reals
    ; event-congruent =
        \ S T equivalenceS measurableS ->
          generated-congruent equivalenceS measurableS
    ; event-empty = generated-empty
    ; event-complement =
        \ S measurableS -> generated-complement measurableS
    ; event-countable-union = generated-countable-union
    }

record ExactProbabilityMeasure
  {R A : Set}
  (reals : CompleteOrderedField R)
  (events : ExactMeasurableSpace A) : Set2 where
  field
    measure :
      Predicate A ->
      R
    measure-congruent :
      (S T : Predicate A) ->
      ((x : A) -> Iff (S x) (T x)) ->
      measure S == measure T
    measure-empty :
      measure emptySet == zeroR reals
    measure-nonnegative :
      (S : Predicate A) ->
      lessOrEqualR reals (zeroR reals) (measure S)
    measure-monotone :
      (S T : Predicate A) ->
      Subset S T ->
      lessOrEqualR reals (measure S) (measure T)
    measure-below-measurable-superset :
      (S T : Predicate A) ->
      event events T ->
      Subset S T ->
      lessOrEqualR reals (measure S) (measure T)
    measure-is-measurable-envelope-infimum :
      (S : Predicate A) ->
      (lower : R) ->
      ((T : Predicate A) ->
        event events T ->
        Subset S T ->
        lessOrEqualR reals lower (measure T)) ->
      lessOrEqualR reals lower (measure S)
    subset-of-measurable-null-is-null :
      (S N : Predicate A) ->
      Subset S N ->
      event events N ->
      measure N == zeroR reals ->
      measure S == zeroR reals
    measure-congruent-outside-null :
      (S T N : Predicate A) ->
      event events N ->
      measure N == zeroR reals ->
      ((x : A) -> Not (N x) -> Iff (S x) (T x)) ->
      measure S == measure T
    measure-countable-additive :
      (sets : Nat -> Predicate A) ->
      ((n : Nat) -> event events (sets n)) ->
      PairwiseDisjoint sets ->
      SequentialLimit reals
        (\ x y -> absoluteR reals (subtractR reals x y))
        (\ count -> sumFirst reals (\ n -> measure (sets n)) count)
        (measure (countableUnion sets))
    measure-total :
      measure wholeSet == oneR reals

open ExactProbabilityMeasure

ExactMeasurableFunction :
  {A B : Set} ->
  ExactMeasurableSpace A ->
  ExactMeasurableSpace B ->
  (A -> B) ->
  Set1
ExactMeasurableFunction source target f =
  (S : Predicate _) ->
  event target S ->
  event source (preimage f S)

record AlmostEverywhere
  {R A : Set}
  {reals : CompleteOrderedField R}
  {events : ExactMeasurableSpace A}
  (probability : ExactProbabilityMeasure reals events)
  (property : Predicate A) : Set2 where
  field
    exceptional-set :
      Predicate A
    exceptional-set-measurable :
      event events exceptional-set
    exceptional-set-null :
      measure probability exceptional-set == zeroR reals
    property-off-exceptional-set :
      (x : A) ->
      Not (exceptional-set x) ->
      property x

record AEMeasurableReal
  {R A : Set}
  {reals : CompleteOrderedField R}
  {events : ExactMeasurableSpace A}
  (probability : ExactProbabilityMeasure reals events)
  (f : A -> R) : Set2 where
  field
    measurable-representative :
      A -> R
    representative-measurable :
      ExactMeasurableFunction
        events
        (realBorelEvents reals)
        measurable-representative
    equal-almost-everywhere :
      AlmostEverywhere probability
        (\ x -> f x == measurable-representative x)

open AEMeasurableReal

record JordanParts
  {R A : Set}
  (reals : CompleteOrderedField R)
  (f positivePart negativePart : A -> R) : Set where
  field
    positive-part-nonnegative :
      (x : A) ->
      lessOrEqualR reals (zeroR reals) (positivePart x)
    negative-part-nonnegative :
      (x : A) ->
      lessOrEqualR reals (zeroR reals) (negativePart x)
    parts-disjoint :
      (x : A) ->
      multiplyR reals (positivePart x) (negativePart x) ==
      zeroR reals
    parts-difference :
      (x : A) ->
      f x == subtractR reals (positivePart x) (negativePart x)

record SimpleNonnegativeFunction
  {R A : Set}
  (reals : CompleteOrderedField R)
  (events : ExactMeasurableSpace A)
  (probability : ExactProbabilityMeasure reals events)
  (f : A -> R) : Set2 where
  field
    simple-cutoff :
      Nat
    simple-index :
      A -> Nat
    simple-values :
      Nat -> R
    simple-index-within :
      (x : A) ->
      simple-index x <=N simple-cutoff
    simple-fibers-measurable :
      (i : Nat) ->
      i <=N simple-cutoff ->
      event events (\ x -> simple-index x == i)
    simple-values-nonnegative :
      (i : Nat) ->
      i <=N simple-cutoff ->
      lessOrEqualR reals (zeroR reals) (simple-values i)
    simple-below-almost-everywhere :
      AlmostEverywhere probability
        (\ x ->
          lessOrEqualR reals
            (simple-values (simple-index x))
            (f x))

open SimpleNonnegativeFunction

simpleLebesgueIntegral :
  {R A : Set}
  {reals : CompleteOrderedField R}
  {events : ExactMeasurableSpace A}
  {probability : ExactProbabilityMeasure reals events}
  {f : A -> R} ->
  SimpleNonnegativeFunction reals events probability f ->
  R
simpleLebesgueIntegral {reals = reals} {probability = probability} simple =
  sumFirst reals
    (\ i ->
      multiplyR reals
        (simple-values simple i)
        (measure probability (\ x -> simple-index simple x == i)))
    (suc (simple-cutoff simple))

record ExactLowerIntegralValue
  {R A : Set}
  (reals : CompleteOrderedField R)
  (events : ExactMeasurableSpace A)
  (probability : ExactProbabilityMeasure reals events)
  (f : A -> R)
  (value : R) : Set2 where
  field
    function-nonnegative-almost-everywhere :
      AlmostEverywhere probability
        (\ x -> lessOrEqualR reals (zeroR reals) (f x))
    upper-bound-for-simple-integrals :
      (simple : SimpleNonnegativeFunction reals events probability f) ->
      lessOrEqualR reals (simpleLebesgueIntegral simple) value
    least-upper-bound-for-simple-integrals :
      (upper : R) ->
      ((simple : SimpleNonnegativeFunction reals events probability f) ->
        lessOrEqualR reals (simpleLebesgueIntegral simple) upper) ->
      lessOrEqualR reals value upper

record ExactLebesgueIntegralValue
  {R A : Set}
  (reals : CompleteOrderedField R)
  (events : ExactMeasurableSpace A)
  (probability : ExactProbabilityMeasure reals events)
  (f : A -> R)
  (value : R) : Set2 where
  field
    ae-measurable :
      AEMeasurableReal probability f
    positive-part :
      A -> R
    negative-part :
      A -> R
    canonical-parts :
      JordanParts reals f positive-part negative-part
    positive-integral-value :
      R
    negative-integral-value :
      R
    positive-integral :
      ExactLowerIntegralValue
        reals events probability positive-part positive-integral-value
    negative-integral :
      ExactLowerIntegralValue
        reals events probability negative-part negative-integral-value
    integral-difference :
      value ==
      subtractR reals positive-integral-value negative-integral-value

square :
  {R : Set} ->
  CompleteOrderedField R ->
  R ->
  R
square reals x =
  multiplyR reals x x

record MemLpTwo
  {R A : Set}
  (reals : CompleteOrderedField R)
  (events : ExactMeasurableSpace A)
  (probability : ExactProbabilityMeasure reals events)
  (f : A -> R) : Set2 where
  field
    square-integral-value :
      R
    square-integrable :
      ExactLebesgueIntegralValue
        reals events probability
        (\ x -> square reals (f x))
        square-integral-value
    mean-value :
      R
    mean-integral :
      ExactLebesgueIntegralValue
        reals events probability f mean-value
    variance-value :
      R
    variance-integral :
      ExactLebesgueIntegralValue
        reals events probability
        (\ x -> square reals (subtractR reals (f x) mean-value))
        variance-value
    variance-nonnegative :
      lessOrEqualR reals (zeroR reals) variance-value

open MemLpTwo

data Member {A : Set} (x : A) : List A -> Set where
  member-here :
    {xs : List A} ->
    Member x (x ∷ xs)
  member-there :
    {y : A} {xs : List A} ->
    Member x xs ->
    Member x (y ∷ xs)

data NoDuplicates {A : Set} : List A -> Set where
  no-duplicates-empty :
    NoDuplicates []
  no-duplicates-cons :
    {x : A} {xs : List A} ->
    Not (Member x xs) ->
    NoDuplicates xs ->
    NoDuplicates (x ∷ xs)

finiteIntersection :
  {R A : Set} ->
  (X : Nat -> A -> R) ->
  (sets : Nat -> Predicate R) ->
  List Nat ->
  Predicate A
finiteIntersection X sets [] =
  wholeSet
finiteIntersection X sets (i ∷ indices) =
  intersection
    (preimage (X i) (sets i))
    (finiteIntersection X sets indices)

finiteMeasureProduct :
  {R A : Set} ->
  {events : ExactMeasurableSpace A} ->
  (reals : CompleteOrderedField R) ->
  ExactProbabilityMeasure reals events ->
  (representatives : Nat -> A -> R) ->
  (sets : Nat -> Predicate R) ->
  List Nat ->
  R
finiteMeasureProduct reals probability representatives sets [] =
  oneR reals
finiteMeasureProduct reals probability representatives sets (i ∷ indices) =
  multiplyR reals
    (measure probability (preimage (representatives i) (sets i)))
    (finiteMeasureProduct
      reals probability representatives sets indices)

record IndependentFunctions
  {R A : Set}
  (reals : CompleteOrderedField R)
  (events : ExactMeasurableSpace A)
  (probability : ExactProbabilityMeasure reals events)
  (X : Nat -> A -> R) : Set2 where
  field
    coordinate-ae-measurable :
      (i : Nat) ->
      AEMeasurableReal probability (X i)
    independent-finite-cylinders :
      (representatives :
        (i : Nat) -> AEMeasurableReal probability (X i)) ->
      (indices : List Nat) ->
      NoDuplicates indices ->
      (sets : Nat -> Predicate R) ->
      ((i : Nat) ->
        Member i indices ->
        RealBorelEvent reals (sets i)) ->
      measure probability
        (finiteIntersection
          (\ i -> measurable-representative (representatives i))
          sets indices) ==
      finiteMeasureProduct reals probability
        (\ i -> measurable-representative (representatives i))
        sets indices

record IdenticallyDistributed
  {R A : Set}
  (reals : CompleteOrderedField R)
  (events : ExactMeasurableSpace A)
  (probability : ExactProbabilityMeasure reals events)
  (f g : A -> R) : Set2 where
  field
    first-ae-measurable :
      AEMeasurableReal probability f
    second-ae-measurable :
      AEMeasurableReal probability g
    equal-pushforward-masses :
      (first-representative : AEMeasurableReal probability f) ->
      (second-representative : AEMeasurableReal probability g) ->
      (S : Predicate R) ->
      RealBorelEvent reals S ->
      measure probability
        (preimage
          (measurable-representative first-representative)
          S) ==
      measure probability
        (preimage
          (measurable-representative second-representative)
          S)

RealLaw :
  {R : Set} ->
  CompleteOrderedField R ->
  Set2
RealLaw reals =
  ExactProbabilityMeasure reals (realBorelEvents reals)

record ExactPushforwardLaw
  {R A : Set}
  (reals : CompleteOrderedField R)
  (events : ExactMeasurableSpace A)
  (probability : ExactProbabilityMeasure reals events)
  (f : A -> R)
  (law : RealLaw reals) : Set2 where
  field
    pushforward-ae-measurable :
      AEMeasurableReal probability f
    pushforward-on-borel-events :
      (representative : AEMeasurableReal probability f) ->
      (S : Predicate R) ->
      RealBorelEvent reals S ->
      measure law S ==
      measure probability
        (preimage (measurable-representative representative) S)

powerSeriesPartialSum :
  {R : Set} ->
  CompleteOrderedField R ->
  (Nat -> R) ->
  Nat ->
  R
powerSeriesPartialSum =
  sumFirst

record ExponentialValue
  {R : Set}
  (reals : CompleteOrderedField R)
  (x value : R) : Set1 where
  field
    terms :
      Nat -> R
    first-term :
      terms zero == oneR reals
    successive-terms :
      (n : Nat) ->
      terms (suc n) ==
      multiplyR reals
        (multiplyR reals (terms n) x)
        (reciprocalR reals (fromNatR reals (suc n)))
    series-limit :
      SequentialLimit reals
        (\ a b -> absoluteR reals (subtractR reals a b))
        (powerSeriesPartialSum reals terms)
        value

record CosineValue
  {R : Set}
  (reals : CompleteOrderedField R)
  (x value : R) : Set1 where
  field
    terms :
      Nat -> R
    first-term :
      terms zero == oneR reals
    successive-terms :
      (n : Nat) ->
      terms (suc n) ==
      multiplyR reals
        (negateR reals
          (multiplyR reals (terms n) (square reals x)))
        (reciprocalR reals
          (multiplyR reals
            (fromNatR reals (suc (n + n)))
            (fromNatR reals (suc (suc (n + n))))))
    series-limit :
      SequentialLimit reals
        (\ a b -> absoluteR reals (subtractR reals a b))
        (powerSeriesPartialSum reals terms)
        value

record SineValue
  {R : Set}
  (reals : CompleteOrderedField R)
  (x value : R) : Set1 where
  field
    terms :
      Nat -> R
    first-term :
      terms zero == x
    successive-terms :
      (n : Nat) ->
      terms (suc n) ==
      multiplyR reals
        (negateR reals
          (multiplyR reals (terms n) (square reals x)))
        (reciprocalR reals
          (multiplyR reals
            (fromNatR reals (suc (suc (n + n))))
            (fromNatR reals (suc (suc (suc (n + n)))))))
    series-limit :
      SequentialLimit reals
        (\ a b -> absoluteR reals (subtractR reals a b))
        (powerSeriesPartialSum reals terms)
        value

record GaussianCosineWitness
  {R A : Set}
  (reals : CompleteOrderedField R)
  (events : ExactMeasurableSpace A)
  (probability : ExactProbabilityMeasure reals events)
  (Y : A -> R)
  (t variance : R) : Set2 where
  field
    cosine-values :
      A -> R
    cosine-values-canonical :
      (x : A) ->
      CosineValue reals
        (multiplyR reals t (Y x))
        (cosine-values x)
    cosine-integral-value :
      R
    cosine-integral :
      ExactLebesgueIntegralValue
        reals events probability
        cosine-values
        cosine-integral-value
    gaussian-exponential :
      ExponentialValue reals
        (negateR reals
          (multiplyR reals
            (multiplyR reals variance (square reals t))
            (reciprocalR reals (fromNatR reals (suc (suc zero))))))
        cosine-integral-value

record GaussianSineWitness
  {R A : Set}
  (reals : CompleteOrderedField R)
  (events : ExactMeasurableSpace A)
  (probability : ExactProbabilityMeasure reals events)
  (Y : A -> R)
  (t : R) : Set2 where
  field
    sine-values :
      A -> R
    sine-values-canonical :
      (x : A) ->
      SineValue reals
        (multiplyR reals t (Y x))
        (sine-values x)
    sine-integral :
      ExactLebesgueIntegralValue
        reals events probability
        sine-values
        (zeroR reals)

record HasCanonicalCenteredGaussianLaw
  {R A : Set}
  (reals : CompleteOrderedField R)
  (events : ExactMeasurableSpace A)
  (probability : ExactProbabilityMeasure reals events)
  (Y : A -> R)
  (variance : R) : Set2 where
  field
    gaussian-ae-measurable :
      AEMeasurableReal probability Y
    gaussian-variance-nonnegative :
      lessOrEqualR reals (zeroR reals) variance
    zero-variance-is-dirac :
      variance == zeroR reals ->
      AlmostEverywhere probability (\ x -> Y x == zeroR reals)
    gaussian-cosine-characteristic :
      (t : R) ->
      GaussianCosineWitness reals events probability Y t variance
    gaussian-sine-characteristic :
      (t : R) ->
      GaussianSineWitness reals events probability Y t

record WeakTestWitness
  {R : Set}
  (reals : CompleteOrderedField R)
  (laws : Nat -> RealLaw reals)
  (limitLaw : RealLaw reals)
  (test : R -> R) : Set2 where
  field
    approximating-integrals :
      Nat -> R
    approximating-integral-definitions :
      (n : Nat) ->
      ExactLebesgueIntegralValue
        reals
        (realBorelEvents reals)
        (laws n)
        test
        (approximating-integrals n)
    limit-integral :
      R
    limit-integral-definition :
      ExactLebesgueIntegralValue
        reals
        (realBorelEvents reals)
        limitLaw
        test
        limit-integral
    integral-limit :
      SequentialLimit reals
        (\ a b -> absoluteR reals (subtractR reals a b))
        approximating-integrals
        limit-integral

record ExactWeakConvergence
  {R : Set}
  (reals : CompleteOrderedField R)
  (laws : Nat -> RealLaw reals)
  (limitLaw : RealLaw reals) : Set2 where
  field
    bounded-continuous-tests :
      (test : R -> R) ->
      Bounded reals test ->
      ((x : R) ->
        (epsilon : R) ->
        Positive reals epsilon ->
        Exists R
          (\ delta ->
            Both
              (Positive reals delta)
              ((y : R) ->
                StrictLess reals
                  (absoluteR reals (subtractR reals y x))
                  delta ->
                StrictLess reals
                  (absoluteR reals
                    (subtractR reals (test y) (test x)))
                  epsilon))) ->
      WeakTestWitness reals laws limitLaw test

record TendstoInDistribution
  {R A B : Set}
  (reals : CompleteOrderedField R)
  (sourceEvents : ExactMeasurableSpace A)
  (sourceProbability : ExactProbabilityMeasure reals sourceEvents)
  (targetEvents : ExactMeasurableSpace B)
  (targetProbability : ExactProbabilityMeasure reals targetEvents)
  (randomVariables : Nat -> A -> R)
  (limitVariable : B -> R) : Set2 where
  field
    approximating-laws :
      Nat -> RealLaw reals
    limit-law :
      RealLaw reals
    approximating-laws-are-pushforwards :
      (n : Nat) ->
      ExactPushforwardLaw
        reals sourceEvents sourceProbability
        (randomVariables n)
        (approximating-laws n)
    limit-law-is-pushforward :
      ExactPushforwardLaw
        reals targetEvents targetProbability
        limitVariable
        limit-law
    pushforward-laws-converge-weakly :
      ExactWeakConvergence reals approximating-laws limit-law

partialSum :
  {R A : Set} ->
  CompleteOrderedField R ->
  (Nat -> A -> R) ->
  Nat ->
  A ->
  R
partialSum reals X zero x =
  zeroR reals
partialSum reals X (suc n) x =
  addR reals (partialSum reals X n x) (X n x)

record PositiveSquareRootNormalizedValue
  {R A : Set}
  (reals : CompleteOrderedField R)
  (X : Nat -> A -> R)
  (mean : R)
  (normalized : Nat -> A -> R)
  (n : Nat)
  (x : A) : Set1 where
  field
    root :
      R
    root-nonnegative :
      lessOrEqualR reals (zeroR reals) root
    root-square :
      square reals root == fromNatR reals (suc n)
    normalized-value :
      normalized (suc n) x ==
      multiplyR reals
        (reciprocalR reals root)
        (subtractR reals
          (partialSum reals X (suc n) x)
          (multiplyR reals
            (fromNatR reals (suc n))
            mean))

record NormalizedCenteredSums
  {R A : Set}
  (reals : CompleteOrderedField R)
  (X : Nat -> A -> R)
  (mean : R)
  (normalized : Nat -> A -> R) : Set1 where
  field
    zero-sum-value :
      (x : A) ->
      normalized zero x == zeroR reals
    positive-sum-values :
      (n : Nat) ->
      (x : A) ->
      PositiveSquareRootNormalizedValue
        reals X mean normalized n x

record CentralLimitConclusion
  {R A B : Set}
  (reals : CompleteOrderedField R)
  (sourceEvents : ExactMeasurableSpace A)
  (sourceProbability : ExactProbabilityMeasure reals sourceEvents)
  (targetEvents : ExactMeasurableSpace B)
  (targetProbability : ExactProbabilityMeasure reals targetEvents)
  (X : Nat -> A -> R)
  (mean : R)
  (Y : B -> R) : Set2 where
  field
    normalized-centered-sums :
      Nat -> A -> R
    normalized-centered-definition :
      NormalizedCenteredSums
        reals X mean normalized-centered-sums
    normalized-laws-converge-to-Y :
      TendstoInDistribution
        reals
        sourceEvents sourceProbability
        targetEvents targetProbability
        normalized-centered-sums Y

central-limit-theorem : Set2
central-limit-theorem =
  (R A B : Set) ->
  (reals : CompleteOrderedField R) ->
  (sourceEvents : ExactMeasurableSpace A) ->
  (sourceProbability : ExactProbabilityMeasure reals sourceEvents) ->
  (targetEvents : ExactMeasurableSpace B) ->
  (targetProbability : ExactProbabilityMeasure reals targetEvents) ->
  (X : Nat -> A -> R) ->
  (Y : B -> R) ->
  (hX : MemLpTwo reals sourceEvents sourceProbability (X zero)) ->
  HasCanonicalCenteredGaussianLaw
    reals targetEvents targetProbability Y (variance-value hX) ->
  IndependentFunctions reals sourceEvents sourceProbability X ->
  ((i : Nat) ->
    IdenticallyDistributed
      reals sourceEvents sourceProbability (X i) (X zero)) ->
  CentralLimitConclusion
    reals
    sourceEvents sourceProbability
    targetEvents targetProbability
    X
    (mean-value hX)
    Y
