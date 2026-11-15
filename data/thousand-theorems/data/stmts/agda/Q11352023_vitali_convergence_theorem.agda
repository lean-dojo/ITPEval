-- Statement-only formalization of thousand-theorems corpus artifact Q11352023,
-- "Vitali convergence theorem": for 1 <= p < infinity, convergence in measure
-- together with uniform integrability and uniform tightness is equivalent to
-- convergence in the Lp seminorm. This file contains no proof.

{-# OPTIONS --safe #-}

module Q11352023_vitali_convergence_theorem where

open import Agda.Primitive using (Level; _⊔_)
open import Agda.Builtin.Equality renaming (_≡_ to _==_)
open import Agda.Builtin.Nat using (Nat; zero; suc)

infix 4 _!=_ _<=N_

data Bottom : Set where

Not : Set -> Set
Not A =
  A -> Bottom

Not1 : Set1 -> Set1
Not1 A =
  A -> Bottom

_!=_ : {A : Set} -> A -> A -> Set
x != y =
  Not (x == y)

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

record BothL
  {a b : Level}
  (A : Set a)
  (B : Set b) :
  Set (a ⊔ b) where
  constructor bothL
  field
    firstL  : A
    secondL : B

record IffL
  {a b : Level}
  (A : Set a)
  (B : Set b) :
  Set (a ⊔ b) where
  constructor equivalenceL
  field
    forwardL  : A -> B
    backwardL : B -> A

record ExistsL
  {a b : Level}
  (A : Set a)
  (P : A -> Set b) :
  Set (a ⊔ b) where
  constructor witnessL
  field
    valueL    : A
    propertyL : P valueL

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

    one-not-zeroR :
      oneR != zeroR

    add-commutativeR :
      (x y : R) -> addR x y == addR y x
    add-associativeR :
      (x y z : R) ->
      addR (addR x y) z == addR x (addR y z)
    add-zeroR :
      (x : R) -> addR x zeroR == x
    add-inverseR :
      (x : R) -> addR x (negateR x) == zeroR

    multiply-commutativeR :
      (x y : R) -> multiplyR x y == multiplyR y x
    multiply-associativeR :
      (x y z : R) ->
      multiplyR (multiplyR x y) z == multiplyR x (multiplyR y z)
    multiply-oneR :
      (x : R) -> multiplyR x oneR == x
    multiply-zeroR :
      (x : R) -> multiplyR x zeroR == zeroR
    distributeR :
      (x y z : R) ->
      multiplyR x (addR y z) ==
      addR (multiplyR x y) (multiplyR x z)
    reciprocal-zeroR :
      reciprocalR zeroR == zeroR
    multiply-reciprocalR :
      (x : R) ->
      x != zeroR ->
      multiplyR x (reciprocalR x) == oneR

    order-reflexiveR :
      (x : R) -> lessOrEqualR x x
    order-transitiveR :
      (x y z : R) ->
      lessOrEqualR x y ->
      lessOrEqualR y z ->
      lessOrEqualR x z
    order-antisymmetricR :
      (x y : R) ->
      lessOrEqualR x y ->
      lessOrEqualR y x ->
      x == y
    order-totalR :
      (x y : R) ->
      Either (lessOrEqualR x y) (lessOrEqualR y x)
    add-orderR :
      (x y z : R) ->
      lessOrEqualR x y ->
      lessOrEqualR (addR z x) (addR z y)
    multiply-nonnegativeR :
      (x y : R) ->
      lessOrEqualR zeroR x ->
      lessOrEqualR zeroR y ->
      lessOrEqualR zeroR (multiplyR x y)
    zero-less-than-oneR :
      Both (lessOrEqualR zeroR oneR) (zeroR != oneR)

    absolute-nonnegativeR :
      (x : R) -> lessOrEqualR zeroR (absoluteR x)
    absolute-of-nonnegativeR :
      (x : R) ->
      lessOrEqualR zeroR x ->
      absoluteR x == x
    absolute-of-nonpositiveR :
      (x : R) ->
      lessOrEqualR x zeroR ->
      absoluteR x == negateR x

    fromNat-zeroR :
      fromNatR zero == zeroR
    fromNat-successorR :
      (n : Nat) ->
      fromNatR (suc n) == addR (fromNatR n) oneR
    fromNat-injectiveR :
      (m n : Nat) ->
      fromNatR m == fromNatR n ->
      m == n

    archimedeanR :
      (x : R) ->
      Exists Nat (\ n -> lessOrEqualR x (fromNatR n))
    least-upper-boundR :
      (P : R -> Set) ->
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

StrictLessR :
  {R : Set} ->
  CompleteOrderedField R ->
  R ->
  R ->
  Set
StrictLessR reals x y =
  Both (lessOrEqualR reals x y) (x != y)

PositiveR :
  {R : Set} ->
  CompleteOrderedField R ->
  R ->
  Set
PositiveR reals x =
  StrictLessR reals (zeroR reals) x

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

record RealPower
  {R : Set}
  (reals : CompleteOrderedField R) : Set1 where
  field
    powerR :
      R -> R -> R
    power-nonnegativeR :
      (x q : R) ->
      lessOrEqualR reals (zeroR reals) x ->
      lessOrEqualR reals (zeroR reals) (powerR x q)
    power-one-exponentR :
      (x : R) ->
      lessOrEqualR reals (zeroR reals) x ->
      powerR x (oneR reals) == x
    power-one-baseR :
      (q : R) ->
      powerR (oneR reals) q == oneR reals
    power-add-exponentsR :
      (x q r : R) ->
      PositiveR reals x ->
      powerR x (addR reals q r) ==
      multiplyR reals (powerR x q) (powerR x r)
    power-multiply-exponentsR :
      (x q r : R) ->
      PositiveR reals x ->
      powerR (powerR x q) r ==
      powerR x (multiplyR reals q r)
    power-strict-monotone-baseR :
      (x y q : R) ->
      lessOrEqualR reals (zeroR reals) x ->
      StrictLessR reals x y ->
      PositiveR reals q ->
      StrictLessR reals (powerR x q) (powerR y q)

open RealPower

record NormedAddCommGroup
  {R : Set}
  (E : Set)
  (reals : CompleteOrderedField R) : Set1 where
  field
    zeroE :
      E
    addE :
      E -> E -> E
    negateE :
      E -> E
    normE :
      E -> R

    add-commutativeE :
      (x y : E) ->
      addE x y == addE y x
    add-associativeE :
      (x y z : E) ->
      addE (addE x y) z == addE x (addE y z)
    add-zeroE :
      (x : E) ->
      addE x zeroE == x
    add-inverseE :
      (x : E) ->
      addE x (negateE x) == zeroE

    norm-nonnegativeE :
      (x : E) ->
      lessOrEqualR reals (zeroR reals) (normE x)
    norm-zeroE :
      normE zeroE == zeroR reals
    norm-zero-onlyE :
      (x : E) ->
      normE x == zeroR reals ->
      x == zeroE
    norm-negateE :
      (x : E) ->
      normE (negateE x) == normE x
    norm-addE :
      (x y : E) ->
      lessOrEqualR reals
        (normE (addE x y))
        (addR reals (normE x) (normE y))

open NormedAddCommGroup

subtractE :
  {R E : Set} ->
  {reals : CompleteOrderedField R} ->
  NormedAddCommGroup E reals ->
  E ->
  E ->
  E
subtractE group x y =
  addE group x (negateE group y)

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
  (x : A) ->
  S x ->
  T x

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
    measurable :
      Predicate A -> Set
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
CanonicalENNRealLe {reals = reals}
  (finite-ennreal x) (finite-ennreal y) =
  lessOrEqualR reals (realValue x) (realValue y)
CanonicalENNRealLe (finite-ennreal x) infinity-ennreal =
  Top
CanonicalENNRealLe infinity-ennreal (finite-ennreal y) =
  Bottom
CanonicalENNRealLe infinity-ennreal infinity-ennreal =
  Top

record ExtendedNonnegativeReals
  (R M : Set)
  (reals : CompleteOrderedField R)
  (realPower : RealPower reals) : Set1 where
  field
    zeroM oneM infinityM :
      M
    addM multiplyM :
      M -> M -> M
    lessOrEqualM :
      M -> M -> Set
    finiteM :
      (x : R) ->
      lessOrEqualR reals (zeroR reals) x ->
      M
    toRealM :
      M -> R
    powerM :
      M -> R -> M

    zero-leastM :
      (x : M) ->
      lessOrEqualM zeroM x
    infinity-greatestM :
      (x : M) ->
      lessOrEqualM x infinityM
    infinity-not-zeroM :
      infinityM != zeroM
    order-reflexiveM :
      (x : M) ->
      lessOrEqualM x x
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
      (x y : M) ->
      Either (lessOrEqualM x y) (lessOrEqualM y x)

    add-commutativeM :
      (x y : M) ->
      addM x y == addM y x
    add-associativeM :
      (x y z : M) ->
      addM (addM x y) z == addM x (addM y z)
    add-zeroM :
      (x : M) ->
      addM x zeroM == x
    add-infinityM :
      (x : M) ->
      addM x infinityM == infinityM
    add-monotoneM :
      (w x y z : M) ->
      lessOrEqualM w x ->
      lessOrEqualM y z ->
      lessOrEqualM (addM w y) (addM x z)

    multiply-commutativeM :
      (x y : M) ->
      multiplyM x y == multiplyM y x
    multiply-associativeM :
      (x y z : M) ->
      multiplyM (multiplyM x y) z ==
      multiplyM x (multiplyM y z)
    multiply-oneM :
      (x : M) ->
      multiplyM x oneM == x
    multiply-zeroM :
      (x : M) ->
      multiplyM x zeroM == zeroM
    multiply-distributesM :
      (x y z : M) ->
      multiplyM x (addM y z) ==
      addM (multiplyM x y) (multiplyM x z)

    finite-zeroM :
      finiteM
        (zeroR reals)
        (order-reflexiveR reals (zeroR reals)) ==
      zeroM
    finite-oneM :
      finiteM
        (oneR reals)
        (Both.first (zero-less-than-oneR reals)) ==
      oneM
    finite-orderM :
      (x y : R) ->
      (hx : lessOrEqualR reals (zeroR reals) x) ->
      (hy : lessOrEqualR reals (zeroR reals) y) ->
      Iff
        (lessOrEqualM (finiteM x hx) (finiteM y hy))
        (lessOrEqualR reals x y)
    finite-addM :
      (x y : R) ->
      (hx : lessOrEqualR reals (zeroR reals) x) ->
      (hy : lessOrEqualR reals (zeroR reals) y) ->
      Exists
        (lessOrEqualR reals (zeroR reals) (addR reals x y))
        (\ hsum ->
          addM (finiteM x hx) (finiteM y hy) ==
          finiteM (addR reals x y) hsum)
    finite-multiplyM :
      (x y : R) ->
      (hx : lessOrEqualR reals (zeroR reals) x) ->
      (hy : lessOrEqualR reals (zeroR reals) y) ->
      Exists
        (lessOrEqualR reals (zeroR reals) (multiplyR reals x y))
        (\ hproduct ->
          multiplyM (finiteM x hx) (finiteM y hy) ==
          finiteM (multiplyR reals x y) hproduct)
    finite-or-infinityM :
      (x : M) ->
      Either
        (x == infinityM)
        (Exists R
          (\ value ->
            Exists
              (lessOrEqualR reals (zeroR reals) value)
              (\ nonnegative ->
                x == finiteM value nonnegative)))

    toReal-finiteM :
      (x : R) ->
      (hx : lessOrEqualR reals (zeroR reals) x) ->
      toRealM (finiteM x hx) == x
    toReal-infinityM :
      toRealM infinityM == zeroR reals
    power-finiteM :
      (x q : R) ->
      (hx : lessOrEqualR reals (zeroR reals) x) ->
      powerM (finiteM x hx) q ==
      finiteM
        (powerR realPower x q)
        (power-nonnegativeR realPower x q hx)
    power-infinity-positiveM :
      (q : R) ->
      PositiveR reals q ->
      powerM infinityM q == infinityM

    supremumM :
      Predicate M -> M
    supremum-upperM :
      (P : Predicate M) ->
      (x : M) ->
      P x ->
      lessOrEqualM x (supremumM P)
    supremum-leastM :
      (P : Predicate M) ->
      (upper : M) ->
      ((x : M) ->
        P x ->
        lessOrEqualM x upper) ->
      lessOrEqualM (supremumM P) upper

open ExtendedNonnegativeReals

record ENNRealPresentation
  {R M : Set}
  {reals : CompleteOrderedField R}
  {realPower : RealPower reals}
  (extended : ExtendedNonnegativeReals R M reals realPower) : Set1 where
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
      toCanonicalENNReal
        (finiteM extended
          (realValue x)
          (realValue-nonnegative x)) ==
      finite-ennreal x
    infinity-correspondenceENNReal :
      toCanonicalENNReal (infinityM extended) == infinity-ennreal
    order-correspondenceENNReal :
      (x y : M) ->
      Iff
        (lessOrEqualM extended x y)
        (CanonicalENNRealLe
          (toCanonicalENNReal x)
          (toCanonicalENNReal y))

sumFirstM :
  {R M : Set} ->
  {reals : CompleteOrderedField R} ->
  {realPower : RealPower reals} ->
  ExtendedNonnegativeReals R M reals realPower ->
  (Nat -> M) ->
  Nat ->
  M
sumFirstM {reals = reals} extended terms zero =
  zeroM extended
sumFirstM extended terms (suc n) =
  addM extended (sumFirstM extended terms n) (terms n)

CountableSum :
  {R M : Set} ->
  {reals : CompleteOrderedField R} ->
  {realPower : RealPower reals} ->
  ExtendedNonnegativeReals R M reals realPower ->
  (Nat -> M) ->
  M ->
  Set
CountableSum extended terms value =
  Both
    ((n : Nat) ->
      lessOrEqualM extended (sumFirstM extended terms n) value)
    ((upper : _) ->
      ((n : Nat) ->
        lessOrEqualM extended (sumFirstM extended terms n) upper) ->
      lessOrEqualM extended value upper)

record Measure
  {A R M : Set}
  {reals : CompleteOrderedField R}
  {realPower : RealPower reals}
  (extended : ExtendedNonnegativeReals R M reals realPower)
  (events : SigmaAlgebra A) : Set1 where
  field
    outerMass :
      Predicate A -> M
    measurableHull :
      Predicate A -> Predicate A
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
  {realPower : RealPower reals} ->
  {extended : ExtendedNonnegativeReals R M reals realPower} ->
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
    function :
      A -> V
    cutoff :
      Nat
    values :
      Nat -> V
    pieces :
      Nat -> Predicate A
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
          Both (i <=N cutoff) (pieces i x))
    represented-on-pieces :
      (i : Nat) ->
      i <=N cutoff ->
      (x : A) ->
      pieces i x ->
      function x == values i

open SimpleFunction

distanceE :
  {R E : Set} ->
  {reals : CompleteOrderedField R} ->
  NormedAddCommGroup E reals ->
  E ->
  E ->
  R
distanceE group x y =
  normE group (subtractE group x y)

SequentialLimitR :
  {R V : Set} ->
  CompleteOrderedField R ->
  (V -> V -> R) ->
  (Nat -> V) ->
  V ->
  Set
SequentialLimitR {R = R} reals distance sequence limit =
  (epsilon : R) ->
  PositiveR reals epsilon ->
  Exists Nat
    (\ cutoff ->
      (n : Nat) ->
      cutoff <=N n ->
      StrictLessR reals (distance (sequence n) limit) epsilon)

record StronglyMeasurable
  {A R E : Set}
  (reals : CompleteOrderedField R)
  (events : SigmaAlgebra A)
  (group : NormedAddCommGroup E reals)
  (f : A -> E) : Set1 where
  field
    approximants :
      Nat -> SimpleFunction {V = E} events
    approximates :
      (x : A) ->
      SequentialLimitR reals (distanceE group)
        (\ n -> function (approximants n) x)
        (f x)

record AEStronglyMeasurable
  {A R M E : Set}
  (reals : CompleteOrderedField R)
  {realPower : RealPower reals}
  {extended : ExtendedNonnegativeReals R M reals realPower}
  (events : SigmaAlgebra A)
  (measure : Measure extended events)
  (group : NormedAddCommGroup E reals)
  (f : A -> E) : Set1 where
  field
    representative :
      A -> E
    representative-strongly-measurable :
      StronglyMeasurable reals events group representative
    equal-almost-everywhere :
      AlmostEverywhere measure (\ x -> f x == representative x)

record Indicator
  {A E : Set}
  (zero : E) : Set1 where
  field
    indicator :
      Predicate A ->
      (A -> E) ->
      A -> E
    indicator-on :
      (S : Predicate A) ->
      (f : A -> E) ->
      (x : A) ->
      S x ->
      indicator S f x == f x
    indicator-off :
      (S : Predicate A) ->
      (f : A -> E) ->
      (x : A) ->
      Not (S x) ->
      indicator S f x == zero

open Indicator

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

sumThroughM :
  {R M : Set} ->
  {reals : CompleteOrderedField R} ->
  {realPower : RealPower reals} ->
  ExtendedNonnegativeReals R M reals realPower ->
  (Nat -> M) ->
  Nat ->
  M
sumThroughM extended terms zero =
  terms zero
sumThroughM extended terms (suc n) =
  addM extended (sumThroughM extended terms n) (terms (suc n))

record SimpleLowerIntegralValue
  {A R M : Set}
  {reals : CompleteOrderedField R}
  {realPower : RealPower reals}
  (extended : ExtendedNonnegativeReals R M reals realPower)
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
  {realPower : RealPower reals}
  (extended : ExtendedNonnegativeReals R M reals realPower)
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
    least-upper-bound-integral :
      (upper : M) ->
      ((simple : NonnegativeSimpleBelow reals events f) ->
        (simpleValue : M) ->
        SimpleLowerIntegralValue extended measure simple simpleValue ->
        lessOrEqualM extended simpleValue upper) ->
      lessOrEqualM extended value upper

record LowerIntegration
  {A R M : Set}
  (reals : CompleteOrderedField R)
  (realPower : RealPower reals)
  (events : SigmaAlgebra A)
  (extended : ExtendedNonnegativeReals R M reals realPower)
  (measure : Measure extended events) : Set2 where
  field
    lowerIntegral :
      (A -> R) -> M
    lower-integral-definition :
      (f : A -> R) ->
      ((x : A) ->
        lessOrEqualR reals (zeroR reals) (f x)) ->
      LowerIntegralValue extended events measure f (lowerIntegral f)
    lower-integral-unique :
      (f : A -> R) ->
      ((x : A) ->
        lessOrEqualR reals (zeroR reals) (f x)) ->
      (value : M) ->
      LowerIntegralValue extended events measure f value ->
      lowerIntegral f == value

open LowerIntegration

record LpSeminorm
  {A R M E : Set}
  (reals : CompleteOrderedField R)
  (realPower : RealPower reals)
  (events : SigmaAlgebra A)
  (extended : ExtendedNonnegativeReals R M reals realPower)
  (measure : Measure extended events)
  (group : NormedAddCommGroup E reals)
  (integration : LowerIntegration reals realPower events extended measure) :
  Set2 where
  field
    eLpNorm :
      (A -> E) ->
      M ->
      M
    eLpNorm-finite-positive-definition :
      (f : A -> E) ->
      (p : M) ->
      lessOrEqualM extended (oneM extended) p ->
      p != infinityM extended ->
      eLpNorm f p ==
      powerM extended
        (lowerIntegral integration
          (\ x ->
            powerR realPower
              (normE group (f x))
              (toRealM extended p)))
        (reciprocalR reals (toRealM extended p))
    eLpNorm-congruent-almost-everywhere :
      (f g : A -> E) ->
      AlmostEverywhere measure (\ x -> f x == g x) ->
      (p : M) ->
      eLpNorm f p == eLpNorm g p

open LpSeminorm

FiniteM :
  {R M : Set} ->
  {reals : CompleteOrderedField R} ->
  {realPower : RealPower reals} ->
  (extended : ExtendedNonnegativeReals R M reals realPower) ->
  M ->
  Set
FiniteM extended x =
  x != infinityM extended

StrictLessM :
  {R M : Set} ->
  {reals : CompleteOrderedField R} ->
  {realPower : RealPower reals} ->
  ExtendedNonnegativeReals R M reals realPower ->
  M ->
  M ->
  Set
StrictLessM extended x y =
  Both
    (lessOrEqualM extended x y)
    (x != y)

PositiveM :
  {R M : Set} ->
  {reals : CompleteOrderedField R} ->
  {realPower : RealPower reals} ->
  ExtendedNonnegativeReals R M reals realPower ->
  M ->
  Set
PositiveM extended x =
  StrictLessM extended (zeroM extended) x

TendsToZeroM :
  {R M : Set} ->
  {reals : CompleteOrderedField R} ->
  {realPower : RealPower reals} ->
  ExtendedNonnegativeReals R M reals realPower ->
  (Nat -> M) ->
  Set
TendsToZeroM {M = M} extended sequence =
  (epsilon : M) ->
  PositiveM extended epsilon ->
  Exists Nat
    (\ cutoff ->
      (n : Nat) ->
      cutoff <=N n ->
      lessOrEqualM extended (sequence n) epsilon)

enorm :
  {R M E : Set} ->
  {reals : CompleteOrderedField R} ->
  {realPower : RealPower reals} ->
  (extended : ExtendedNonnegativeReals R M reals realPower) ->
  (group : NormedAddCommGroup E reals) ->
  E ->
  M
enorm extended group x =
  finiteM extended
    (normE group x)
    (norm-nonnegativeE group x)

edistance :
  {R M E : Set} ->
  {reals : CompleteOrderedField R} ->
  {realPower : RealPower reals} ->
  (extended : ExtendedNonnegativeReals R M reals realPower) ->
  (group : NormedAddCommGroup E reals) ->
  E ->
  E ->
  M
edistance extended group x y =
  enorm extended group (subtractE group x y)

record MemLp
  {A R M E : Set}
  {reals : CompleteOrderedField R}
  {realPower : RealPower reals}
  {events : SigmaAlgebra A}
  {extended : ExtendedNonnegativeReals R M reals realPower}
  {measure : Measure extended events}
  {group : NormedAddCommGroup E reals}
  {integration : LowerIntegration reals realPower events extended measure}
  (lp : LpSeminorm
    reals realPower events extended measure group integration)
  (f : A -> E)
  (p : M) : Set1 where
  field
    almost-everywhere-strongly-measurable :
      AEStronglyMeasurable reals events measure group f
    finite-eLpNorm :
      FiniteM extended (eLpNorm lp f p)

TendstoInMeasure :
  {A R M E : Set} ->
  {reals : CompleteOrderedField R} ->
  {realPower : RealPower reals} ->
  {events : SigmaAlgebra A} ->
  (extended : ExtendedNonnegativeReals R M reals realPower) ->
  (measure : Measure extended events) ->
  (group : NormedAddCommGroup E reals) ->
  (Nat -> A -> E) ->
  (A -> E) ->
  Set
TendstoInMeasure {M = M} extended measure group functions limit =
  (epsilon : M) ->
  PositiveM extended epsilon ->
  TendsToZeroM extended
    (\ n ->
      outerMass measure
        (\ x ->
          lessOrEqualM extended epsilon
            (edistance extended group (functions n x) (limit x))))

UnifIntegrable :
  {A R M E : Set} ->
  {reals : CompleteOrderedField R} ->
  {realPower : RealPower reals} ->
  {events : SigmaAlgebra A} ->
  {extended : ExtendedNonnegativeReals R M reals realPower} ->
  {measure : Measure extended events} ->
  {group : NormedAddCommGroup E reals} ->
  {integration : LowerIntegration reals realPower events extended measure} ->
  (lp : LpSeminorm reals realPower events extended measure group integration) ->
  Indicator (zeroE group) ->
  (Nat -> A -> E) ->
  M ->
  Set1
UnifIntegrable {A = A} {R = R} {reals = reals}
  {events = events} {extended = extended} {measure = measure}
  lp indicators functions p =
  (epsilon : R) ->
  (epsilon-positive : PositiveR reals epsilon) ->
  ExistsL R
    (\ delta ->
      ExistsL (PositiveR reals delta)
        (\ delta-positive ->
          (n : Nat) ->
          (S : Predicate A) ->
          measurable events S ->
          lessOrEqualM extended
            (outerMass measure S)
            (finiteM extended delta (Both.first delta-positive)) ->
          lessOrEqualM extended
            (eLpNorm lp (indicator indicators S (functions n)) p)
            (finiteM extended epsilon (Both.first epsilon-positive))))

UnifTight :
  {A R M E : Set} ->
  {reals : CompleteOrderedField R} ->
  {realPower : RealPower reals} ->
  {events : SigmaAlgebra A} ->
  {extended : ExtendedNonnegativeReals R M reals realPower} ->
  {measure : Measure extended events} ->
  {group : NormedAddCommGroup E reals} ->
  {integration : LowerIntegration reals realPower events extended measure} ->
  (lp : LpSeminorm reals realPower events extended measure group integration) ->
  Indicator (zeroE group) ->
  (Nat -> A -> E) ->
  M ->
  Set1
UnifTight {A = A} {R = R} {reals = reals}
  {extended = extended} {measure = measure}
  lp indicators functions p =
  (epsilon : R) ->
  (epsilon-positive : PositiveR reals epsilon) ->
  ExistsL (Predicate A)
    (\ S ->
      Both
        (outerMass measure S != infinityM extended)
        ((n : Nat) ->
          lessOrEqualM extended
            (eLpNorm lp
              (indicator indicators (complement S) (functions n))
              p)
            (finiteM extended epsilon (Both.first epsilon-positive))))

vitali-convergence-theorem : Set2
vitali-convergence-theorem =
  (A R M E : Set) ->
  (reals : CompleteOrderedField R) ->
  RealNumberPresentation reals ->
  (realPower : RealPower reals) ->
  (events : SigmaAlgebra A) ->
  (extended : ExtendedNonnegativeReals R M reals realPower) ->
  ENNRealPresentation extended ->
  (measure : Measure extended events) ->
  (group : NormedAddCommGroup E reals) ->
  (indicators : Indicator (zeroE group)) ->
  (integration : LowerIntegration reals realPower events extended measure) ->
  (lp : LpSeminorm
    reals realPower events extended measure group integration) ->
  (p : M) ->
  lessOrEqualM extended (oneM extended) p ->
  p != infinityM extended ->
  (functions : Nat -> A -> E) ->
  (limit : A -> E) ->
  ((n : Nat) -> MemLp lp (functions n) p) ->
  MemLp lp limit p ->
  IffL
    (BothL
      (TendstoInMeasure extended measure group functions limit)
      (BothL
        (UnifIntegrable lp indicators functions p)
        (UnifTight lp indicators functions p)))
    (TendsToZeroM extended
      (\ n ->
        eLpNorm lp
          (\ x -> subtractE group (functions n x) (limit x))
          p))
