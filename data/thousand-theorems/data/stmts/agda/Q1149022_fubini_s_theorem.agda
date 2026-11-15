-- Statement-only formalization of thousand-theorems corpus artifact Q1149022,
-- "Fubini's theorem": the Bochner integral of an integrable function with
-- respect to the product of two s-finite measures equals its iterated integral.
-- This file contains no proof.

{-# OPTIONS --safe #-}

module Q1149022_fubini_s_theorem where

open import Agda.Builtin.Equality renaming (_≡_ to _==_)
open import Agda.Builtin.Nat using (Nat; zero; suc)

infix 4 _!=_ _<=N_

data Bottom : Set where

Not : Set -> Set
Not A = A -> Bottom

Not1 : Set1 -> Set1
Not1 A = A -> Bottom

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
      (x y : R) -> Either (lessOrEqualR x y) (lessOrEqualR y x)
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
      (x : R) -> lessOrEqualR zeroR (absoluteR x)
    absolute-of-nonnegative :
      (x : R) ->
      lessOrEqualR zeroR x ->
      absoluteR x == x
    absolute-of-nonpositive :
      (x : R) ->
      lessOrEqualR x zeroR ->
      absoluteR x == negateR x
    absolute-zero-only :
      (x : R) -> absoluteR x == zeroR -> x == zeroR
    absolute-negate :
      (x : R) -> absoluteR (negateR x) == absoluteR x
    absolute-add :
      (x y : R) ->
      lessOrEqualR (absoluteR (addR x y))
        (addR (absoluteR x) (absoluteR y))
    absolute-multiply :
      (x y : R) ->
      absoluteR (multiplyR x y) ==
      multiplyR (absoluteR x) (absoluteR y)

    fromNat-zero :
      fromNatR zero == zeroR
    fromNat-successor :
      (n : Nat) -> fromNatR (suc n) == addR (fromNatR n) oneR
    fromNat-injective :
      (m n : Nat) -> fromNatR m == fromNatR n -> m == n

    archimedean :
      (x : R) -> Exists Nat (\ n -> lessOrEqualR x (fromNatR n))
    least-upper-bound :
      (P : R -> Set) ->
      Exists R P ->
      Exists R (\ upper -> (x : R) -> P x -> lessOrEqualR x upper) ->
      Exists R
        (\ supremum ->
          Both
            ((x : R) -> P x -> lessOrEqualR x supremum)
            ((upper : R) ->
              ((x : R) -> P x -> lessOrEqualR x upper) ->
              lessOrEqualR supremum upper))

open CompleteOrderedField

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

record NormedVectorSpace
  (R E : Set)
  (reals : CompleteOrderedField R) : Set1 where
  field
    zeroE : E
    addE : E -> E -> E
    negateE : E -> E
    scaleE : R -> E -> E
    normE : E -> R

    add-commutativeE :
      (x y : E) -> addE x y == addE y x
    add-associativeE :
      (x y z : E) -> addE (addE x y) z == addE x (addE y z)
    add-zeroE :
      (x : E) -> addE x zeroE == x
    add-inverseE :
      (x : E) -> addE x (negateE x) == zeroE

    scale-one :
      (x : E) -> scaleE (oneR reals) x == x
    scale-associative :
      (a b : R) ->
      (x : E) ->
      scaleE (multiplyR reals a b) x == scaleE a (scaleE b x)
    scale-add-vectors :
      (a : R) ->
      (x y : E) ->
      scaleE a (addE x y) == addE (scaleE a x) (scaleE a y)
    scale-add-scalars :
      (a b : R) ->
      (x : E) ->
      scaleE (addR reals a b) x == addE (scaleE a x) (scaleE b x)

    norm-nonnegative :
      (x : E) -> lessOrEqualR reals (zeroR reals) (normE x)
    norm-zero :
      normE zeroE == zeroR reals
    norm-zero-only :
      (x : E) -> normE x == zeroR reals -> x == zeroE
    norm-negate :
      (x : E) -> normE (negateE x) == normE x
    norm-add :
      (x y : E) ->
      lessOrEqualR reals (normE (addE x y))
        (addR reals (normE x) (normE y))
    norm-scale :
      (a : R) ->
      (x : E) ->
      normE (scaleE a x) == multiplyR reals (absoluteR reals a) (normE x)

open NormedVectorSpace

subtractE :
  {R E : Set} ->
  {reals : CompleteOrderedField R} ->
  NormedVectorSpace R E reals ->
  E ->
  E ->
  E
subtractE space x y =
  addE space x (negateE space y)

distanceR :
  {R : Set} ->
  CompleteOrderedField R ->
  R ->
  R ->
  R
distanceR reals x y =
  absoluteR reals (subtractR reals x y)

distanceE :
  {R E : Set} ->
  {reals : CompleteOrderedField R} ->
  NormedVectorSpace R E reals ->
  E ->
  E ->
  R
distanceE space x y =
  normE space (subtractE space x y)

SequentialLimit :
  {R V : Set} ->
  CompleteOrderedField R ->
  (V -> V -> R) ->
  (Nat -> V) ->
  V ->
  Set
SequentialLimit {R = R} reals distance sequence limit =
  (epsilon : R) ->
  Positive reals epsilon ->
  Exists Nat
    (\ cutoff ->
      (n : Nat) ->
      cutoff <=N n ->
      StrictLess reals (distance (sequence n) limit) epsilon)

CauchySequence :
  {R V : Set} ->
  CompleteOrderedField R ->
  (V -> V -> R) ->
  (Nat -> V) ->
  Set
CauchySequence {R = R} reals distance sequence =
  (epsilon : R) ->
  Positive reals epsilon ->
  Exists Nat
    (\ cutoff ->
      (m n : Nat) ->
      cutoff <=N m ->
      cutoff <=N n ->
      StrictLess reals (distance (sequence m) (sequence n)) epsilon)

Complete :
  {R V : Set} ->
  CompleteOrderedField R ->
  (V -> V -> R) ->
  Set
Complete {V = V} reals distance =
  (sequence : Nat -> V) ->
  CauchySequence reals distance sequence ->
  Exists V (\ limit -> SequentialLimit reals distance sequence limit)

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
Subset {A = A} S T =
  (x : A) -> S x -> T x

PairwiseDisjoint :
  {A : Set} ->
  (Nat -> Predicate A) ->
  Set
PairwiseDisjoint {A = A} sets =
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

record ExtendedNonnegativeReals
  (R M : Set)
  (reals : CompleteOrderedField R) : Set1 where
  field
    zeroM oneM infinityM : M
    addM multiplyM : M -> M -> M
    lessOrEqualM : M -> M -> Set
    finiteM : (x : R) -> lessOrEqualR reals (zeroR reals) x -> M

    zero-least :
      (x : M) -> lessOrEqualM zeroM x
    infinity-greatest :
      (x : M) -> lessOrEqualM x infinityM
    infinity-not-zero :
      infinityM != zeroM
    order-reflexiveM :
      (x : M) -> lessOrEqualM x x
    order-transitiveM :
      (x y z : M) ->
      lessOrEqualM x y ->
      lessOrEqualM y z ->
      lessOrEqualM x z
    order-antisymmetricM :
      (x y : M) ->
      lessOrEqualM x y ->
      lessOrEqualM y x ->
      x == y
    order-totalM :
      (x y : M) -> Either (lessOrEqualM x y) (lessOrEqualM y x)

    add-commutativeM :
      (x y : M) -> addM x y == addM y x
    add-associativeM :
      (x y z : M) -> addM (addM x y) z == addM x (addM y z)
    add-zeroM :
      (x : M) -> addM x zeroM == x
    add-infinityM :
      (x : M) -> addM x infinityM == infinityM
    add-monotoneM :
      (w x y z : M) ->
      lessOrEqualM w x ->
      lessOrEqualM y z ->
      lessOrEqualM (addM w y) (addM x z)
    multiply-commutativeM :
      (x y : M) -> multiplyM x y == multiplyM y x
    multiply-associativeM :
      (x y z : M) ->
      multiplyM (multiplyM x y) z == multiplyM x (multiplyM y z)
    multiply-oneM :
      (x : M) -> multiplyM x oneM == x
    multiply-zeroM :
      (x : M) -> multiplyM x zeroM == zeroM
    multiply-distributesM :
      (x y z : M) ->
      multiplyM x (addM y z) ==
      addM (multiplyM x y) (multiplyM x z)
    multiply-monotoneM :
      (w x y z : M) ->
      lessOrEqualM w x ->
      lessOrEqualM y z ->
      lessOrEqualM (multiplyM w y) (multiplyM x z)

    finite-zero :
      finiteM (zeroR reals) (order-reflexive reals (zeroR reals)) == zeroM
    finite-one :
      finiteM (oneR reals) (Both.first (zero-less-than-one reals)) == oneM
    finite-order :
      (x y : R) ->
      (hx : lessOrEqualR reals (zeroR reals) x) ->
      (hy : lessOrEqualR reals (zeroR reals) y) ->
      Iff (lessOrEqualM (finiteM x hx) (finiteM y hy))
        (lessOrEqualR reals x y)
    finite-add :
      (x y : R) ->
      (hx : lessOrEqualR reals (zeroR reals) x) ->
      (hy : lessOrEqualR reals (zeroR reals) y) ->
      Exists
        (lessOrEqualR reals (zeroR reals) (addR reals x y))
        (\ hsum ->
          addM (finiteM x hx) (finiteM y hy) ==
          finiteM (addR reals x y) hsum)
    finite-multiply :
      (x y : R) ->
      (hx : lessOrEqualR reals (zeroR reals) x) ->
      (hy : lessOrEqualR reals (zeroR reals) y) ->
      Exists
        (lessOrEqualR reals (zeroR reals) (multiplyR reals x y))
        (\ hproduct ->
          multiplyM (finiteM x hx) (finiteM y hy) ==
          finiteM (multiplyR reals x y) hproduct)
    finite-or-infinity :
      (x : M) ->
      Either
        (x == infinityM)
        (Exists R
          (\ value ->
            Exists
              (lessOrEqualR reals (zeroR reals) value)
              (\ nonnegative -> x == finiteM value nonnegative)))
    multiply-infinity-nonzero :
      (x : M) ->
      x != zeroM ->
      multiplyM x infinityM == infinityM

    supremumM : Predicate M -> M
    supremum-upper :
      (P : Predicate M) ->
      (x : M) ->
      P x ->
      lessOrEqualM x (supremumM P)
    supremum-least :
      (P : Predicate M) ->
      (upper : M) ->
      ((x : M) -> P x -> lessOrEqualM x upper) ->
      lessOrEqualM (supremumM P) upper

open ExtendedNonnegativeReals

sumFirstM :
  {R M : Set} ->
  {reals : CompleteOrderedField R} ->
  ExtendedNonnegativeReals R M reals ->
  (Nat -> M) ->
  Nat ->
  M
sumFirstM {reals = reals} extended terms zero =
  zeroM extended
sumFirstM extended terms (suc n) =
  addM extended (sumFirstM extended terms n) (terms n)

sumThroughM :
  {R M : Set} ->
  {reals : CompleteOrderedField R} ->
  ExtendedNonnegativeReals R M reals ->
  (Nat -> M) ->
  Nat ->
  M
sumThroughM extended terms zero =
  terms zero
sumThroughM extended terms (suc n) =
  addM extended (sumThroughM extended terms n) (terms (suc n))

CountableSum :
  {R M : Set} ->
  {reals : CompleteOrderedField R} ->
  ExtendedNonnegativeReals R M reals ->
  (Nat -> M) ->
  M ->
  Set
CountableSum extended terms value =
  Both
    ((n : Nat) -> lessOrEqualM extended (sumFirstM extended terms n) value)
    ((upper : _) ->
      ((n : Nat) ->
        lessOrEqualM extended (sumFirstM extended terms n) upper) ->
      lessOrEqualM extended value upper)

record Measure
  {A R M : Set}
  {reals : CompleteOrderedField R}
  (extended : ExtendedNonnegativeReals R M reals)
  (events : SigmaAlgebra A) : Set1 where
  field
    outerMass : Predicate A -> M
    measurableHull : Predicate A -> Predicate A

    outer-mass-congruent :
      (S T : Predicate A) ->
      ((x : A) -> Iff (S x) (T x)) ->
      outerMass S == outerMass T
    measurable-hull-measurable :
      (S : Predicate A) ->
      measurable events (measurableHull S)
    subset-measurable-hull :
      (S : Predicate A) ->
      Subset S (measurableHull S)
    outer-mass-measurable-hull :
      (S : Predicate A) ->
      outerMass (measurableHull S) == outerMass S
    outer-mass-empty :
      outerMass emptySet == zeroM extended
    outer-mass-monotone :
      (S T : Predicate A) ->
      Subset S T ->
      lessOrEqualM extended (outerMass S) (outerMass T)
    outer-countable-subadditive :
      (sets : Nat -> Predicate A) ->
      (sumValue : M) ->
      CountableSum extended
        (\ n -> outerMass (sets n))
        sumValue ->
      lessOrEqualM extended
        (outerMass (countableUnion sets))
        sumValue
    measurable-caratheodory :
      (S : Predicate A) ->
      measurable events S ->
      (T : Predicate A) ->
      outerMass T ==
      addM extended
        (outerMass (intersection T S))
        (outerMass (intersection T (complement S)))
    measurable-countable-additivity :
      (sets : Nat -> Predicate A) ->
      ((n : Nat) -> measurable events (sets n)) ->
      PairwiseDisjoint sets ->
      CountableSum extended
        (\ n -> outerMass (sets n))
        (outerMass (countableUnion sets))

open Measure

AlmostEverywhere :
  {A R M : Set} ->
  {reals : CompleteOrderedField R} ->
  {extended : ExtendedNonnegativeReals R M reals} ->
  {events : SigmaAlgebra A} ->
  Measure extended events ->
  Predicate A ->
  Set
AlmostEverywhere {extended = extended} measure property =
  outerMass measure (\ x -> Not (property x)) == zeroM extended

record SimpleFunction
  {A V : Set}
  (events : SigmaAlgebra A) : Set1 where
  field
    function : A -> V
    cutoff : Nat
    values : Nat -> V
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
      Exists Nat (\ i -> Both (i <=N cutoff) (pieces i x))
    represented-on-pieces :
      (i : Nat) ->
      i <=N cutoff ->
      (x : A) ->
      pieces i x ->
      function x == values i

open SimpleFunction

record StronglyMeasurable
  {A R V : Set}
  (reals : CompleteOrderedField R)
  (events : SigmaAlgebra A)
  (distance : V -> V -> R)
  (f : A -> V) : Set1 where
  field
    approximants :
      Nat -> SimpleFunction {V = V} events
    approximates :
      (x : A) ->
      SequentialLimit reals distance
        (\ n -> function (approximants n) x)
        (f x)

record AEStronglyMeasurable
  {A R M V : Set}
  (reals : CompleteOrderedField R)
  {extended : ExtendedNonnegativeReals R M reals}
  (events : SigmaAlgebra A)
  (measure : Measure extended events)
  (distance : V -> V -> R)
  (f : A -> V) : Set1 where
  field
    representative :
      A -> V
    representative-strongly-measurable :
      StronglyMeasurable reals events distance representative
    equal-almost-everywhere :
      AlmostEverywhere measure (\ x -> f x == representative x)

record NonnegativeSimpleBelow
  {A R : Set}
  (reals : CompleteOrderedField R)
  (events : SigmaAlgebra A)
  (f : A -> R) : Set1 where
  field
    underlying :
      SimpleFunction {A = A} {V = R} events
    values-nonnegative :
      (i : Nat) ->
      lessOrEqualR reals
        (zeroR reals)
        (values underlying i)
    pointwise-below :
      (x : A) ->
      lessOrEqualR reals
        (function underlying x)
        (f x)

open NonnegativeSimpleBelow

record SimpleLowerIntegralValue
  {A R M : Set}
  {reals : CompleteOrderedField R}
  (extended : ExtendedNonnegativeReals R M reals)
  {events : SigmaAlgebra A}
  (measure : Measure extended events)
  {f : A -> R}
  (simple : NonnegativeSimpleBelow reals events f)
  (value : M) : Set1 where
  field
    integral-equation :
      value ==
      sumThroughM extended
        (\ i ->
          multiplyM extended
            (finiteM extended
              (values (underlying simple) i)
              (values-nonnegative simple i))
            (outerMass measure (pieces (underlying simple) i)))
        (cutoff (underlying simple))

record LowerIntegralValue
  {A R M : Set}
  {reals : CompleteOrderedField R}
  (extended : ExtendedNonnegativeReals R M reals)
  (events : SigmaAlgebra A)
  (measure : Measure extended events)
  (f : A -> R)
  (value : M) : Set1 where
  field
    simple-integrals-below :
      (simple : NonnegativeSimpleBelow reals events f) ->
      (simpleValue : M) ->
      SimpleLowerIntegralValue extended measure simple simpleValue ->
      lessOrEqualM extended simpleValue value
    least-upper-bound :
      (upper : M) ->
      ((simple : NonnegativeSimpleBelow reals events f) ->
        (simpleValue : M) ->
        SimpleLowerIntegralValue extended measure simple simpleValue ->
        lessOrEqualM extended simpleValue upper) ->
      lessOrEqualM extended value upper

record ExtendedSimpleBelow
  {A R M : Set}
  {reals : CompleteOrderedField R}
  (extended : ExtendedNonnegativeReals R M reals)
  (events : SigmaAlgebra A)
  (f : A -> M) : Set1 where
  field
    underlying :
      SimpleFunction {A = A} {V = M} events
    pointwise-below :
      (x : A) ->
      lessOrEqualM extended
        (function underlying x)
        (f x)

open ExtendedSimpleBelow

record SimpleLIntegralValue
  {A R M : Set}
  {reals : CompleteOrderedField R}
  (extended : ExtendedNonnegativeReals R M reals)
  {events : SigmaAlgebra A}
  (measure : Measure extended events)
  {f : A -> M}
  (simple : ExtendedSimpleBelow extended events f)
  (value : M) : Set1 where
  field
    integral-equation :
      value ==
      sumThroughM extended
        (\ i ->
          multiplyM extended
            (values (underlying simple) i)
            (outerMass measure (pieces (underlying simple) i)))
        (cutoff (underlying simple))

record LIntegralValue
  {A R M : Set}
  {reals : CompleteOrderedField R}
  (extended : ExtendedNonnegativeReals R M reals)
  (events : SigmaAlgebra A)
  (measure : Measure extended events)
  (f : A -> M)
  (value : M) : Set1 where
  field
    simple-integrals-below :
      (simple : ExtendedSimpleBelow extended events f) ->
      (simpleValue : M) ->
      SimpleLIntegralValue extended measure simple simpleValue ->
      lessOrEqualM extended simpleValue value
    least-upper-bound :
      (upper : M) ->
      ((simple : ExtendedSimpleBelow extended events f) ->
        (simpleValue : M) ->
        SimpleLIntegralValue extended measure simple simpleValue ->
        lessOrEqualM extended simpleValue upper) ->
      lessOrEqualM extended value upper

record RealIntegrability
  {A R M : Set}
  (reals : CompleteOrderedField R)
  (events : SigmaAlgebra A)
  (extended : ExtendedNonnegativeReals R M reals)
  (measure : Measure extended events)
  (lowerIntegral : (A -> R) -> M)
  (f : A -> R) : Set1 where
  field
    strongly-measurable :
      AEStronglyMeasurable reals events measure (distanceR reals) f
    absolute-integral-definition :
      LowerIntegralValue extended events measure
        (\ x -> absoluteR reals (f x))
        (lowerIntegral (\ x -> absoluteR reals (f x)))
    absolute-integral-finite :
      lowerIntegral (\ x -> absoluteR reals (f x)) != infinityM extended

record VectorIntegrable
  {A R M E : Set}
  (reals : CompleteOrderedField R)
  (space : NormedVectorSpace R E reals)
  (events : SigmaAlgebra A)
  (extended : ExtendedNonnegativeReals R M reals)
  (measure : Measure extended events)
  (f : A -> E) : Set1 where
  field
    strongly-measurable :
      AEStronglyMeasurable reals events measure (distanceE space) f
    norm-integral :
      M
    norm-integral-definition :
      LowerIntegralValue extended events measure
        (\ x -> normE space (f x))
        norm-integral
    norm-integral-finite :
      norm-integral != infinityM extended

sumThroughE :
  {R E : Set} ->
  {reals : CompleteOrderedField R} ->
  NormedVectorSpace R E reals ->
  (Nat -> E) ->
  Nat ->
  E
sumThroughE space terms zero =
  terms zero
sumThroughE space terms (suc n) =
  addE space (sumThroughE space terms n) (terms (suc n))

data PieceBochnerIntegralValue
  {A R M E : Set}
  {reals : CompleteOrderedField R}
  (space : NormedVectorSpace R E reals)
  {extended : ExtendedNonnegativeReals R M reals}
  {events : SigmaAlgebra A}
  (measure : Measure extended events)
  (coefficient : E)
  (piece : Predicate A)
  (value : E) : Set1 where
  zero-coefficient-value :
    coefficient == zeroE space ->
    value == zeroE space ->
    PieceBochnerIntegralValue space measure coefficient piece value
  finite-mass-value :
    (mass : R) ->
    (mass-nonnegative :
      lessOrEqualR reals (zeroR reals) mass) ->
    outerMass measure piece ==
      finiteM extended mass mass-nonnegative ->
    value == scaleE space mass coefficient ->
    PieceBochnerIntegralValue space measure coefficient piece value

record SimpleBochnerIntegralValue
  {A R M E : Set}
  {reals : CompleteOrderedField R}
  (space : NormedVectorSpace R E reals)
  {extended : ExtendedNonnegativeReals R M reals}
  (events : SigmaAlgebra A)
  (measure : Measure extended events)
  (simple : SimpleFunction {A = A} {V = E} events)
  (value : E) : Set1 where
  field
    terms :
      Nat -> E
    term-definition :
      (i : Nat) ->
      i <=N cutoff simple ->
      PieceBochnerIntegralValue space measure
        (values simple i)
        (pieces simple i)
        (terms i)
    integral-equation :
      value == sumThroughE space terms (cutoff simple)

record BochnerLimitValue
  {A R M E : Set}
  (reals : CompleteOrderedField R)
  (space : NormedVectorSpace R E reals)
  (events : SigmaAlgebra A)
  (extended : ExtendedNonnegativeReals R M reals)
  (measure : Measure extended events)
  (f : A -> E)
  (value : E) : Set1 where
  field
    approximants :
      Nat -> SimpleFunction {A = A} {V = E} events
    approximant-integrals :
      Nat -> E
    approximant-integral-definitions :
      (n : Nat) ->
      SimpleBochnerIntegralValue space events measure
        (approximants n)
        (approximant-integrals n)
    errors :
      Nat -> R
    errors-nonnegative :
      (n : Nat) ->
      lessOrEqualR reals (zeroR reals) (errors n)
    errors-represent-lower-integrals :
      (n : Nat) ->
      LowerIntegralValue extended events measure
        (\ x ->
          normE space
            (subtractE space
              (function (approximants n) x)
              (f x)))
        (finiteM extended (errors n) (errors-nonnegative n))
    errors-tend-to-zero :
      SequentialLimit reals (distanceR reals)
        errors
        (zeroR reals)
    approximant-integrals-tend-to-value :
      SequentialLimit reals (distanceE space)
        approximant-integrals
        value

data TotalizedBochnerIntegralValue
  {A R M E : Set}
  (reals : CompleteOrderedField R)
  (space : NormedVectorSpace R E reals)
  (events : SigmaAlgebra A)
  (extended : ExtendedNonnegativeReals R M reals)
  (measure : Measure extended events)
  (f : A -> E)
  (value : E) : Set1 where
  complete-integrable-value :
    Complete reals (distanceE space) ->
    VectorIntegrable
      reals space events extended measure f ->
    BochnerLimitValue
      reals space events extended measure f value ->
    TotalizedBochnerIntegralValue
      reals space events extended measure f value
  nonintegrable-value :
    Not1
      (VectorIntegrable
        reals space events extended measure f) ->
    value == zeroE space ->
    TotalizedBochnerIntegralValue
      reals space events extended measure f value
  incomplete-space-value :
    Not (Complete reals (distanceE space)) ->
    value == zeroE space ->
    TotalizedBochnerIntegralValue
      reals space events extended measure f value

record Pair (A B : Set) : Set where
  constructor _,_
  field
    firstOf  : A
    secondOf : B

open Pair

Rectangle :
  {A B : Set} ->
  Predicate A ->
  Predicate B ->
  Predicate (Pair A B)
Rectangle S T pair =
  Both (S (firstOf pair)) (T (secondOf pair))

rightSection :
  {A B : Set} ->
  Predicate (Pair A B) ->
  A ->
  Predicate B
rightSection U x y =
  U (x , y)

record ProductSigmaAlgebra
  {A B : Set}
  (eventsA : SigmaAlgebra A)
  (eventsB : SigmaAlgebra B)
  (eventsAB : SigmaAlgebra (Pair A B)) : Set1 where
  field
    rectangles-measurable :
      (S : Predicate A) ->
      (T : Predicate B) ->
      measurable eventsA S ->
      measurable eventsB T ->
      measurable eventsAB (Rectangle S T)
    generated-by-rectangles :
      (candidate : SigmaAlgebra (Pair A B)) ->
      ((S : Predicate A) ->
        (T : Predicate B) ->
        measurable eventsA S ->
        measurable eventsB T ->
        measurable candidate (Rectangle S T)) ->
      (U : Predicate (Pair A B)) ->
      measurable eventsAB U ->
      measurable candidate U

FiniteMeasure :
  {A R M : Set} ->
  {reals : CompleteOrderedField R} ->
  {extended : ExtendedNonnegativeReals R M reals} ->
  {events : SigmaAlgebra A} ->
  Measure extended events ->
  Set
FiniteMeasure {extended = extended} measure =
  outerMass measure wholeSet != infinityM extended

record SFiniteMeasure
  {A R M : Set}
  {reals : CompleteOrderedField R}
  {extended : ExtendedNonnegativeReals R M reals}
  {events : SigmaAlgebra A}
  (measure : Measure extended events) : Set1 where
  field
    finite-parts :
      Nat -> Measure extended events
    each-part-finite :
      (n : Nat) ->
      FiniteMeasure (finite-parts n)
    parts-sum-to-measure :
      (S : Predicate _) ->
      measurable events S ->
      CountableSum extended
        (\ n -> outerMass (finite-parts n) S)
        (outerMass measure S)

record CanonicalMeasureOperations
  {R M E : Set}
  (reals : CompleteOrderedField R)
  (space : NormedVectorSpace R E reals)
  (extended : ExtendedNonnegativeReals R M reals)
  : Set2 where
  field
    productEvents :
      {A B : Set} ->
      SigmaAlgebra A ->
      SigmaAlgebra B ->
      SigmaAlgebra (Pair A B)
    product-sigma-definition :
      {A B : Set} ->
      (eventsA : SigmaAlgebra A) ->
      (eventsB : SigmaAlgebra B) ->
      ProductSigmaAlgebra
        eventsA eventsB (productEvents eventsA eventsB)
    productMeasure :
      {A B : Set} ->
      (eventsA : SigmaAlgebra A) ->
      (eventsB : SigmaAlgebra B) ->
      Measure extended eventsA ->
      Measure extended eventsB ->
      Measure extended (productEvents eventsA eventsB)
    product-measure-sfinite :
      {A B : Set} ->
      (eventsA : SigmaAlgebra A) ->
      (eventsB : SigmaAlgebra B) ->
      (measureA : Measure extended eventsA) ->
      (measureB : Measure extended eventsB) ->
      SFiniteMeasure measureA ->
      SFiniteMeasure measureB ->
      SFiniteMeasure
        (productMeasure eventsA eventsB measureA measureB)
    product-measurable-set-construction :
      {A B : Set} ->
      (eventsA : SigmaAlgebra A) ->
      (eventsB : SigmaAlgebra B) ->
      (measureA : Measure extended eventsA) ->
      (measureB : Measure extended eventsB) ->
      SFiniteMeasure measureB ->
      (U : Predicate (Pair A B)) ->
      measurable (productEvents eventsA eventsB) U ->
      LIntegralValue extended eventsA measureA
        (\ x -> outerMass measureB (rightSection U x))
        (outerMass
          (productMeasure eventsA eventsB measureA measureB)
          U)
    bochnerIntegral :
      {A : Set} ->
      (events : SigmaAlgebra A) ->
      Measure extended events ->
      (A -> E) ->
      E
    bochner-integral-definition :
      {A : Set} ->
      (events : SigmaAlgebra A) ->
      (measure : Measure extended events) ->
      (f : A -> E) ->
      TotalizedBochnerIntegralValue
        reals space events extended measure f
        (bochnerIntegral events measure f)
    bochner-integral-unique :
      {A : Set} ->
      (events : SigmaAlgebra A) ->
      (measure : Measure extended events) ->
      (f : A -> E) ->
      (value : E) ->
      TotalizedBochnerIntegralValue
        reals space events extended measure f value ->
      bochnerIntegral events measure f == value

open CanonicalMeasureOperations

fubini-s-theorem : Set2
fubini-s-theorem =
  (A B R M E : Set) ->
  (reals : CompleteOrderedField R) ->
  RealNumberPresentation reals ->
  (space : NormedVectorSpace R E reals) ->
  (eventsA : SigmaAlgebra A) ->
  (eventsB : SigmaAlgebra B) ->
  (extended : ExtendedNonnegativeReals R M reals) ->
  (operations :
    CanonicalMeasureOperations reals space extended) ->
  (measureA : Measure extended eventsA) ->
  (measureB : Measure extended eventsB) ->
  (sfiniteA : SFiniteMeasure measureA) ->
  (sfiniteB : SFiniteMeasure measureB) ->
  (f : Pair A B -> E) ->
  VectorIntegrable
    reals space
    (productEvents operations eventsA eventsB)
    extended
    (productMeasure operations eventsA eventsB measureA measureB)
    f ->
  bochnerIntegral operations
    (productEvents operations eventsA eventsB)
    (productMeasure operations eventsA eventsB measureA measureB)
    f ==
  bochnerIntegral operations eventsA measureA
    (\ x ->
      bochnerIntegral operations eventsB measureB
        (\ y -> f (x , y)))
