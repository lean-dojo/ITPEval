-- Statement-only formalization of Hundred Theorems corpus artifact
-- hundred-theorems__agda__099, "Buffon Needle Problem": the crossing probability
-- for a uniformly dropped needle in the short- and long-needle cases. This file
-- contains no proof.

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

record StandardRealAnalysis (R : Set) : Set1 where
  field
    algebra : CompleteOrderedField R
    pi : R
    sine cosine squareRoot arccosine : R -> R

    sine-series :
      (x : R) ->
      SequentialLimit algebra
        (sinePartialSum algebra x)
        (sine x)
    cosine-series :
      (x : R) ->
      SequentialLimit algebra
        (cosinePartialSum algebra x)
        (cosine x)

    pi-positive :
      StrictLess algebra (zeroR algebra) pi
    sine-pi :
      sine pi == zeroR algebra
    cosine-pi :
      cosine pi == negate algebra (oneR algebra)
    pi-least-positive-cosine-minus-one :
      (x : R) ->
      StrictLess algebra (zeroR algebra) x ->
      cosine x == negate algebra (oneR algebra) ->
      lessOrEqual algebra pi x

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

    cosine-arccosine :
      (x : R) ->
      lessOrEqual algebra (negate algebra (oneR algebra)) x ->
      lessOrEqual algebra x (oneR algebra) ->
      cosine (arccosine x) == x
    arccosine-range :
      (x : R) ->
      lessOrEqual algebra (negate algebra (oneR algebra)) x ->
      lessOrEqual algebra x (oneR algebra) ->
      Both
        (lessOrEqual algebra (zeroR algebra) (arccosine x))
        (lessOrEqual algebra (arccosine x) pi)
    arccosine-cosine :
      (x : R) ->
      lessOrEqual algebra (zeroR algebra) x ->
      lessOrEqual algebra x pi ->
      arccosine (cosine x) == x

open StandardRealAnalysis

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

intersection :
  {A : Set} ->
  Predicate A ->
  Predicate A ->
  Predicate A
intersection E F x =
  Both (E x) (F x)

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

record ProbabilitySpace
  {A R : Set}
  (analysis : StandardRealAnalysis R)
  (events : SigmaAlgebra A) : Set1 where
  field
    probability : Predicate A -> R

    probability-congruent :
      (E F : Predicate A) ->
      ((x : A) -> Iff (E x) (F x)) ->
      probability E == probability F
    probability-empty :
      probability emptySet == zeroR (algebra analysis)
    probability-whole :
      probability wholeSet == oneR (algebra analysis)
    probability-nonnegative :
      (E : Predicate A) ->
      measurable events E ->
      lessOrEqual (algebra analysis)
        (zeroR (algebra analysis))
        (probability E)
    countable-additivity :
      (sets : Nat -> Predicate A) ->
      ((n : Nat) -> measurable events (sets n)) ->
      PairwiseDisjoint sets ->
      SequentialLimit (algebra analysis)
        (\ count ->
          sumFirst (algebra analysis)
            (\ n -> probability (sets n))
            count)
        (probability (countableUnion sets))

open ProbabilitySpace

record StandardProbabilityTheory (R : Set) : Set1 where
  field
    analysis : StandardRealAnalysis R
    borel : SigmaAlgebra R
    borel-lower-ray :
      (t : R) ->
      measurable borel
        (\ x -> lessOrEqual (algebra analysis) x t)

open StandardProbabilityTheory

realAlgebra :
  {R : Set} ->
  StandardProbabilityTheory R ->
  CompleteOrderedField R
realAlgebra theory =
  algebra (analysis theory)

distributionFunction :
  {R A : Set}
  {theory : StandardProbabilityTheory R}
  {events : SigmaAlgebra A} ->
  ProbabilitySpace (analysis theory) events ->
  (A -> R) ->
  R ->
  R
distributionFunction {theory = theory} space X t =
  probability space
    (\ x -> lessOrEqual (realAlgebra theory) (X x) t)

record UniformVariable
  {R A : Set}
  (theory : StandardProbabilityTheory R)
  (events : SigmaAlgebra A)
  (space : ProbabilitySpace (analysis theory) events)
  (X : A -> R)
  (a b : R) : Set1 where
  field
    measurable-variable :
      MeasurableFunction events (borel theory) X
    proper-interval :
      StrictLess (realAlgebra theory) a b
    cdf-below :
      (t : R) ->
      StrictLess (realAlgebra theory) t a ->
      distributionFunction {theory = theory} {events = events} space X t ==
      zeroR (realAlgebra theory)
    cdf-middle :
      (t : R) ->
      lessOrEqual (realAlgebra theory) a t ->
      StrictLess (realAlgebra theory) t b ->
      distributionFunction {theory = theory} {events = events} space X t ==
      divide (realAlgebra theory)
        (subtract (realAlgebra theory) t a)
        (subtract (realAlgebra theory) b a)
    cdf-above :
      (t : R) ->
      lessOrEqual (realAlgebra theory) b t ->
      distributionFunction {theory = theory} {events = events} space X t ==
      oneR (realAlgebra theory)

record IndependentVariables
  {R A : Set}
  (theory : StandardProbabilityTheory R)
  (events : SigmaAlgebra A)
  (space : ProbabilitySpace (analysis theory) events)
  (X Y : A -> R) : Set1 where
  field
    independent-events :
      (E F : Predicate R) ->
      measurable (borel theory) E ->
      measurable (borel theory) F ->
      probability space
        (intersection (preimage X E) (preimage Y F)) ==
      multiply (realAlgebra theory)
        (probability space (preimage X E))
        (probability space (preimage Y F))

crossingEvent :
  {R A : Set} ->
  (theory : StandardProbabilityTheory R) ->
  (X theta : A -> R) ->
  R ->
  Predicate A
crossingEvent theory X theta length outcome =
  lessOrEqual reals
    (X outcome)
    (multiply reals
      (divide reals length (fromNat reals (suc (suc zero))))
      (sine (analysis theory) (theta outcome)))
  where
    reals = realAlgebra theory

shortFormula :
  {R : Set} ->
  (theory : StandardProbabilityTheory R) ->
  R ->
  R ->
  R
shortFormula theory length spacing =
  divide reals
    (multiply reals two length)
    (multiply reals piR spacing)
  where
    reals = realAlgebra theory
    two = fromNat reals (suc (suc zero))
    piR = pi (analysis theory)

longFormula :
  {R : Set} ->
  (theory : StandardProbabilityTheory R) ->
  R ->
  R ->
  R
longFormula theory length spacing =
  multiply reals
    (divide reals two (multiply reals piR spacing))
    (add reals
      (subtract reals
        length
        (squareRoot (analysis theory)
          (subtract reals
            (square reals length)
            (square reals spacing))))
      (multiply reals
        spacing
        (arccosine (analysis theory)
          (divide reals spacing length))))
  where
    reals = realAlgebra theory
    two = fromNat reals (suc (suc zero))
    piR = pi (analysis theory)

record BuffonNeedleConclusion
  {R A : Set}
  (theory : StandardProbabilityTheory R)
  (events : SigmaAlgebra A)
  (space : ProbabilitySpace (analysis theory) events)
  (X theta : A -> R)
  (length spacing : R) : Set where
  field
    short-needle :
      lessOrEqual (realAlgebra theory) length spacing ->
      probability space (crossingEvent theory X theta length) ==
      shortFormula theory length spacing
    long-needle :
      lessOrEqual (realAlgebra theory) spacing length ->
      probability space (crossingEvent theory X theta length) ==
      longFormula theory length spacing

buffon-needle-problem : Set1
buffon-needle-problem =
  (R A : Set) ->
  (theory : StandardProbabilityTheory R) ->
  (events : SigmaAlgebra A) ->
  (space : ProbabilitySpace (analysis theory) events) ->
  (X theta : A -> R) ->
  (length spacing : R) ->
  StrictLess (realAlgebra theory)
    (zeroR (realAlgebra theory))
    length ->
  StrictLess (realAlgebra theory)
    (zeroR (realAlgebra theory))
    spacing ->
  UniformVariable theory events space X
    (zeroR (realAlgebra theory))
    (divide (realAlgebra theory)
      spacing
      (fromNat (realAlgebra theory) (suc (suc zero)))) ->
  UniformVariable theory events space theta
    (zeroR (realAlgebra theory))
    (pi (analysis theory)) ->
  IndependentVariables theory events space X theta ->
  BuffonNeedleConclusion
    theory events space X theta length spacing
