-- Statement-only formalization of thousand-theorems corpus artifact Q1067156X,
-- "Bounded convergence theorem": uniformly bounded nonnegative continuous
-- functions converging pointwise, or almost everywhere along a countably
-- generated filter, have convergent lower integrals against a finite measure.
-- This file contains no proof.

{-# OPTIONS --safe #-}

module Q1067156X_bounded_convergence_theorem where

open import Agda.Builtin.Equality renaming (_≡_ to _==_)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.List using (List; []; _∷_)

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

record NonnegativeReal
  {R : Set}
  (reals : CompleteOrderedField R) : Set where
  constructor nonnegative-real
  field
    realValue :
      R
    realValue-nonnegative :
      lessOrEqualR reals (zeroR reals) realValue

open NonnegativeReal

_<=NN_ :
  {R : Set} ->
  {reals : CompleteOrderedField R} ->
  NonnegativeReal reals ->
  NonnegativeReal reals ->
  Set
_<=NN_ {reals = reals} x y =
  lessOrEqualR reals (realValue x) (realValue y)

finiteNN :
  {R M : Set} ->
  {reals : CompleteOrderedField R} ->
  (extended : ExtendedNonnegativeReals R M reals) ->
  NonnegativeReal reals ->
  M
finiteNN extended x =
  finiteM extended (realValue x) (realValue-nonnegative x)

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

data CanonicalENNReal
  {R : Set}
  (reals : CompleteOrderedField R) : Set where
  finite-ennreal :
    NonnegativeReal reals ->
    CanonicalENNReal reals
  infinity-ennreal :
    CanonicalENNReal reals

CanonicalENNRealLe :
  {R : Set} ->
  {reals : CompleteOrderedField R} ->
  CanonicalENNReal reals ->
  CanonicalENNReal reals ->
  Set
CanonicalENNRealLe (finite-ennreal x) (finite-ennreal y) =
  x <=NN y
CanonicalENNRealLe (finite-ennreal x) infinity-ennreal =
  Top
CanonicalENNRealLe infinity-ennreal (finite-ennreal y) =
  Bottom
CanonicalENNRealLe infinity-ennreal infinity-ennreal =
  Top

record ENNRealPresentation
  {R M : Set}
  {reals : CompleteOrderedField R}
  (extended : ExtendedNonnegativeReals R M reals) : Set1 where
  field
    toCanonicalENNReal :
      M -> CanonicalENNReal reals
    fromCanonicalENNReal :
      CanonicalENNReal reals -> M
    to-after-fromENNReal :
      (x : CanonicalENNReal reals) ->
      toCanonicalENNReal (fromCanonicalENNReal x) == x
    from-after-toENNReal :
      (x : M) ->
      fromCanonicalENNReal (toCanonicalENNReal x) == x
    finite-correspondenceENNReal :
      (x : NonnegativeReal reals) ->
      toCanonicalENNReal (finiteNN extended x) == finite-ennreal x
    infinity-correspondenceENNReal :
      toCanonicalENNReal (infinityM extended) == infinity-ennreal
    order-correspondenceENNReal :
      (x y : M) ->
      Iff
        (lessOrEqualM extended x y)
        (CanonicalENNRealLe
          (toCanonicalENNReal x)
          (toCanonicalENNReal y))

record IndexedNonnegativeSimpleBelow
  {A R : Set}
  (reals : CompleteOrderedField R)
  (events : SigmaAlgebra A)
  (f : A -> R) : Set where
  field
    simpleCutoff :
      Nat
    simpleIndex :
      A -> Nat
    simpleValues :
      Nat -> R
    simpleIndexWithin :
      (x : A) ->
      simpleIndex x <=N simpleCutoff
    simpleFiberMeasurable :
      (i : Nat) ->
      i <=N simpleCutoff ->
      measurable events (\ x -> simpleIndex x == i)
    simpleValuesNonnegative :
      (i : Nat) ->
      lessOrEqualR reals (zeroR reals) (simpleValues i)
    simplePointwiseBelow :
      (x : A) ->
      lessOrEqualR reals (simpleValues (simpleIndex x)) (f x)

open IndexedNonnegativeSimpleBelow

indexedSimpleIntegral :
  {A R M : Set} ->
  {reals : CompleteOrderedField R} ->
  {events : SigmaAlgebra A} ->
  (extended : ExtendedNonnegativeReals R M reals) ->
  (measure : Measure extended events) ->
  {f : A -> R} ->
  IndexedNonnegativeSimpleBelow reals events f ->
  M
indexedSimpleIntegral extended measure simple =
  sumThroughM extended
    (\ i ->
      multiplyM extended
        (finiteM extended
          (simpleValues simple i)
          (simpleValuesNonnegative simple i))
        (outerMass measure
          (\ x -> simpleIndex simple x == i)))
    (simpleCutoff simple)

record SimpleIntegralCandidate
  {A R M : Set}
  {reals : CompleteOrderedField R}
  {events : SigmaAlgebra A}
  (extended : ExtendedNonnegativeReals R M reals)
  (measure : Measure extended events)
  (f : A -> R)
  (candidate : M) : Set where
  field
    candidateSimple :
      IndexedNonnegativeSimpleBelow reals events f
    candidateEquation :
      candidate ==
      indexedSimpleIntegral extended measure candidateSimple

canonicalLowerIntegral :
  {A R M : Set} ->
  {reals : CompleteOrderedField R} ->
  {events : SigmaAlgebra A} ->
  (extended : ExtendedNonnegativeReals R M reals) ->
  (measure : Measure extended events) ->
  (A -> R) ->
  M
canonicalLowerIntegral extended measure f =
  supremumM extended
    (\ candidate ->
      SimpleIntegralCandidate extended measure f candidate)

canonicalLowerIntegralNN :
  {A R M : Set} ->
  {reals : CompleteOrderedField R} ->
  {events : SigmaAlgebra A} ->
  (extended : ExtendedNonnegativeReals R M reals) ->
  (measure : Measure extended events) ->
  (A -> NonnegativeReal reals) ->
  M
canonicalLowerIntegralNN extended measure f =
  canonicalLowerIntegral extended measure (\ x -> realValue (f x))

record NeighborhoodRefinement
  {A : Set}
  (near : A -> Predicate A -> Set)
  (x : A)
  (U : Predicate A) : Set1 where
  field
    refinement :
      Predicate A
    refinement-near :
      near x refinement
    refinement-stays-near :
      (y : A) ->
      refinement y ->
      near y U

record TopologicalSpace (A : Set) : Set2 where
  field
    neighborhood :
      A ->
      Predicate A ->
      Set
    neighborhood-contains :
      (x : A) ->
      (U : Predicate A) ->
      neighborhood x U ->
      U x
    neighborhood-whole :
      (x : A) ->
      neighborhood x wholeSet
    neighborhood-upward :
      (x : A) ->
      (U V : Predicate A) ->
      neighborhood x U ->
      Subset U V ->
      neighborhood x V
    neighborhood-intersection :
      (x : A) ->
      (U V : Predicate A) ->
      neighborhood x U ->
      neighborhood x V ->
      neighborhood x (intersection U V)
    neighborhood-local :
      (x : A) ->
      (U : Predicate A) ->
      neighborhood x U ->
      NeighborhoodRefinement neighborhood x U

open TopologicalSpace

IsOpen :
  {A : Set} ->
  TopologicalSpace A ->
  Predicate A ->
  Set
IsOpen {A = A} topology U =
  (x : A) ->
  U x ->
  neighborhood topology x U

OpensMeasurableSpace :
  {A : Set} ->
  TopologicalSpace A ->
  SigmaAlgebra A ->
  Set1
OpensMeasurableSpace topology events =
  (U : _) ->
  IsOpen topology U ->
  measurable events U

StrictLessBy :
  {X : Set} ->
  (X -> X -> Set) ->
  X ->
  X ->
  Set
StrictLessBy le x y =
  Both (le x y) (Not (le y x))

data OrderRay (X : Set) : Set where
  above : X -> OrderRay X
  below : X -> OrderRay X

RayContains :
  {X : Set} ->
  (X -> X -> Set) ->
  OrderRay X ->
  X ->
  Set
RayContains le (above lower) x =
  StrictLessBy le lower x
RayContains le (below upper) x =
  StrictLessBy le x upper

All :
  {X : Set} ->
  (X -> Set) ->
  List X ->
  Set
All P [] =
  Top
All P (x ∷ xs) =
  Both (P x) (All P xs)

BasicContains :
  {X : Set} ->
  (X -> X -> Set) ->
  List (OrderRay X) ->
  X ->
  Set
BasicContains le rays x =
  All (\ ray -> RayContains le ray x) rays

OrderNeighborhood :
  {X : Set} ->
  (X -> X -> Set) ->
  X ->
  Predicate X ->
  Set
OrderNeighborhood {X = X} le x U =
  Exists (List (OrderRay X))
    (\ rays ->
      Both
        (BasicContains le rays x)
        (Subset (BasicContains le rays) U))

record Filter (I : Set) : Set2 where
  field
    eventually :
      Predicate I ->
      Set
    eventually-whole :
      eventually wholeSet
    eventually-upward :
      (P Q : Predicate I) ->
      eventually P ->
      Subset P Q ->
      eventually Q
    eventually-intersection :
      (P Q : Predicate I) ->
      eventually P ->
      eventually Q ->
      eventually (intersection P Q)

open Filter

record CountablyGenerated
  {I : Set}
  (source-filter : Filter I) : Set1 where
  field
    basis :
      Nat ->
      Predicate I
    basis-eventually :
      (n : Nat) ->
      eventually source-filter (basis n)
    eventually-has-basis :
      (P : Predicate I) ->
      eventually source-filter P ->
      Exists Nat (\ n -> Subset (basis n) P)
    basis-generates :
      (P : Predicate I) ->
      Exists Nat (\ n -> Subset (basis n) P) ->
      eventually source-filter P

TendstoNN :
  {I R : Set} ->
  {reals : CompleteOrderedField R} ->
  Filter I ->
  (I -> NonnegativeReal reals) ->
  NonnegativeReal reals ->
  Set
TendstoNN {reals = reals} source-filter sequence limit =
  (rays : List (OrderRay (NonnegativeReal reals))) ->
  BasicContains _<=NN_ rays limit ->
  eventually source-filter
    (\ i -> BasicContains _<=NN_ rays (sequence i))

TendstoM :
  {I R M : Set} ->
  {reals : CompleteOrderedField R} ->
  (extended : ExtendedNonnegativeReals R M reals) ->
  Filter I ->
  (I -> M) ->
  M ->
  Set
TendstoM extended source-filter sequence limit =
  (rays : List (OrderRay _)) ->
  BasicContains (lessOrEqualM extended) rays limit ->
  eventually source-filter
    (\ i ->
      BasicContains (lessOrEqualM extended) rays (sequence i))

EventuallyAtTop :
  (Nat -> Set) ->
  Set
EventuallyAtTop P =
  Exists Nat
    (\ cutoff ->
      (n : Nat) ->
      cutoff <=N n ->
      P n)

SequentialTendstoNN :
  {R : Set} ->
  {reals : CompleteOrderedField R} ->
  (Nat -> NonnegativeReal reals) ->
  NonnegativeReal reals ->
  Set
SequentialTendstoNN {reals = reals} sequence limit =
  (rays : List (OrderRay (NonnegativeReal reals))) ->
  BasicContains _<=NN_ rays limit ->
  EventuallyAtTop
    (\ n -> BasicContains _<=NN_ rays (sequence n))

SequentialTendstoM :
  {R M : Set} ->
  {reals : CompleteOrderedField R} ->
  (extended : ExtendedNonnegativeReals R M reals) ->
  (Nat -> M) ->
  M ->
  Set
SequentialTendstoM extended sequence limit =
  (rays : List (OrderRay _)) ->
  BasicContains (lessOrEqualM extended) rays limit ->
  EventuallyAtTop
    (\ n ->
      BasicContains (lessOrEqualM extended) rays (sequence n))

record BoundedContinuousNN
  {A R : Set}
  (reals : CompleteOrderedField R)
  (topology : TopologicalSpace A) : Set1 where
  field
    applyNN :
      A ->
      NonnegativeReal reals
    continuousNN :
      (x : A) ->
      (rays : List (OrderRay (NonnegativeReal reals))) ->
      BasicContains _<=NN_ rays (applyNN x) ->
      neighborhood topology x
        (\ y -> BasicContains _<=NN_ rays (applyNN y))
    boundedNN :
      Exists (NonnegativeReal reals)
        (\ bound ->
          (x : A) ->
          applyNN x <=NN bound)

open BoundedContinuousNN

FiniteMeasure :
  {A R M : Set} ->
  {reals : CompleteOrderedField R} ->
  {extended : ExtendedNonnegativeReals R M reals} ->
  {events : SigmaAlgebra A} ->
  Measure extended events ->
  Set
FiniteMeasure {extended = extended} measure =
  outerMass measure wholeSet != infinityM extended

tendsto-lintegral-nn-filter-of-le-const : Set2
tendsto-lintegral-nn-filter-of-le-const =
  (A R M I : Set) ->
  (reals : CompleteOrderedField R) ->
  RealNumberPresentation reals ->
  (topology : TopologicalSpace A) ->
  (events : SigmaAlgebra A) ->
  OpensMeasurableSpace topology events ->
  (extended : ExtendedNonnegativeReals R M reals) ->
  ENNRealPresentation extended ->
  (measure : Measure extended events) ->
  FiniteMeasure measure ->
  (source-filter : Filter I) ->
  CountablyGenerated source-filter ->
  (functions : I -> BoundedContinuousNN reals topology) ->
  (constant : NonnegativeReal reals) ->
  eventually source-filter
    (\ i ->
      AlmostEverywhere measure
        (\ x -> applyNN (functions i) x <=NN constant)) ->
  (limit : A -> NonnegativeReal reals) ->
  AlmostEverywhere measure
    (\ x ->
      TendstoNN source-filter
        (\ i -> applyNN (functions i) x)
        (limit x)) ->
  TendstoM extended source-filter
    (\ i ->
      canonicalLowerIntegralNN extended measure (applyNN (functions i)))
    (canonicalLowerIntegralNN extended measure limit)

tendsto-lintegral-nn-of-le-const : Set2
tendsto-lintegral-nn-of-le-const =
  (A R M : Set) ->
  (reals : CompleteOrderedField R) ->
  RealNumberPresentation reals ->
  (topology : TopologicalSpace A) ->
  (events : SigmaAlgebra A) ->
  OpensMeasurableSpace topology events ->
  (extended : ExtendedNonnegativeReals R M reals) ->
  ENNRealPresentation extended ->
  (measure : Measure extended events) ->
  FiniteMeasure measure ->
  (functions : Nat -> BoundedContinuousNN reals topology) ->
  (constant : NonnegativeReal reals) ->
  ((n : Nat) ->
    (x : A) ->
    applyNN (functions n) x <=NN constant) ->
  (limit : A -> NonnegativeReal reals) ->
  ((x : A) ->
    SequentialTendstoNN
      (\ n -> applyNN (functions n) x)
      (limit x)) ->
  SequentialTendstoM extended
    (\ n ->
      canonicalLowerIntegralNN extended measure (applyNN (functions n)))
    (canonicalLowerIntegralNN extended measure limit)
