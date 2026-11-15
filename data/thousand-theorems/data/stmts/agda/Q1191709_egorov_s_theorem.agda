-- Statement-only formalization of thousand-theorems corpus artifact Q1191709,
-- "Egorov's theorem": almost-everywhere convergence of strongly measurable
-- functions on a measurable finite-measure set is uniform outside an
-- arbitrarily small measurable subset. This file contains no proof.

{-# OPTIONS --safe #-}

module Q1191709_egorov_s_theorem where

open import Agda.Primitive using (Level; _⊔_)
open import Agda.Builtin.Equality renaming (_≡_ to _==_)
open import Agda.Builtin.Nat using (Nat; zero; suc)

infix 4 _!=_ _<=N_

data Bottom : Set where

Not : Set -> Set
Not A =
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
    add-nonnegativeR :
      (x y : R) ->
      lessOrEqualR zeroR x ->
      lessOrEqualR zeroR y ->
      lessOrEqualR zeroR (addR x y)
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

Predicate : Set -> Set1
Predicate A =
  A -> Set

emptySet :
  {A : Set} ->
  Predicate A
emptySet _ =
  Bottom

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

difference :
  {A : Set} ->
  Predicate A ->
  Predicate A ->
  Predicate A
difference S T x =
  Both (S x) (Not (T x))

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

CanonicalENNRealAdd :
  {R : Set} ->
  {reals : CompleteOrderedField R} ->
  CanonicalENNReal reals ->
  CanonicalENNReal reals ->
  CanonicalENNReal reals
CanonicalENNRealAdd {reals = reals}
  (finite-ennreal x) (finite-ennreal y) =
  finite-ennreal
    (nonnegative-real
      (addR reals (realValue x) (realValue y))
      (add-nonnegativeR reals
        (realValue x)
        (realValue y)
        (realValue-nonnegative x)
        (realValue-nonnegative y)))
CanonicalENNRealAdd (finite-ennreal x) infinity-ennreal =
  infinity-ennreal
CanonicalENNRealAdd infinity-ennreal (finite-ennreal y) =
  infinity-ennreal
CanonicalENNRealAdd infinity-ennreal infinity-ennreal =
  infinity-ennreal

record ExtendedNonnegativeReals
  (R M : Set)
  (reals : CompleteOrderedField R) : Set1 where
  field
    zeroM infinityM :
      M
    addM :
      M -> M -> M
    lessOrEqualM :
      M -> M -> Set
    finiteM :
      (x : R) ->
      lessOrEqualR reals (zeroR reals) x ->
      M

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

    finite-zeroM :
      finiteM
        (zeroR reals)
        (order-reflexiveR reals (zeroR reals)) ==
      zeroM
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
      addM (finiteM x hx) (finiteM y hy) ==
      finiteM
        (addR reals x y)
        (add-nonnegativeR reals x y hx hy)
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

open ExtendedNonnegativeReals

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
    zero-correspondenceENNReal :
      toCanonicalENNReal (zeroM extended) ==
      finite-ennreal
        (nonnegative-real
          (zeroR reals)
          (order-reflexiveR reals (zeroR reals)))
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
    add-correspondenceENNReal :
      (x y : M) ->
      toCanonicalENNReal (addM extended x y) ==
      CanonicalENNRealAdd
        (toCanonicalENNReal x)
        (toCanonicalENNReal y)

sumFirstM :
  {R M : Set} ->
  {reals : CompleteOrderedField R} ->
  ExtendedNonnegativeReals R M reals ->
  (Nat -> M) ->
  Nat ->
  M
sumFirstM extended terms zero =
  zeroM extended
sumFirstM extended terms (suc n) =
  addM extended (sumFirstM extended terms n) (terms n)

CountableSum :
  {R M : Set} ->
  {reals : CompleteOrderedField R} ->
  ExtendedNonnegativeReals R M reals ->
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
  (extended : ExtendedNonnegativeReals R M reals)
  (events : SigmaAlgebra A) : Set1 where
  field
    outerMass :
      Predicate A -> M
    outer-mass-congruent :
      (S T : Predicate A) ->
      ((x : A) -> Iff (S x) (T x)) ->
      outerMass S == outerMass T
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

record PseudoEMetricSpace
  {R M : Set}
  (E : Set)
  (reals : CompleteOrderedField R)
  (extended : ExtendedNonnegativeReals R M reals) : Set1 where
  field
    edistance :
      E -> E -> M
    edistance-self :
      (x : E) ->
      edistance x x == zeroM extended
    edistance-symmetric :
      (x y : E) ->
      edistance x y == edistance y x
    edistance-triangle :
      (x y z : E) ->
      lessOrEqualM extended
        (edistance x z)
        (addM extended (edistance x y) (edistance y z))

open PseudoEMetricSpace

StrictLessM :
  {R M : Set} ->
  {reals : CompleteOrderedField R} ->
  ExtendedNonnegativeReals R M reals ->
  M ->
  M ->
  Set
StrictLessM extended x y =
  Both
    (lessOrEqualM extended x y)
    (x != y)

TendstoNat :
  {R M E : Set} ->
  {reals : CompleteOrderedField R} ->
  {extended : ExtendedNonnegativeReals R M reals} ->
  PseudoEMetricSpace E reals extended ->
  (Nat -> E) ->
  E ->
  Set
TendstoNat {R = R} {reals = reals} {extended = extended}
  space sequence limit =
  (epsilon : R) ->
  (epsilon-positive : PositiveR reals epsilon) ->
  Exists Nat
    (\ cutoff ->
      (n : Nat) ->
      cutoff <=N n ->
      StrictLessM extended
        (edistance space (sequence n) limit)
        (finiteM extended epsilon (Both.first epsilon-positive)))

record StronglyMeasurable
  {A R M E : Set}
  (reals : CompleteOrderedField R)
  {extended : ExtendedNonnegativeReals R M reals}
  (events : SigmaAlgebra A)
  (space : PseudoEMetricSpace E reals extended)
  (f : A -> E) : Set1 where
  field
    approximants :
      Nat -> SimpleFunction {V = E} events
    approximates :
      (x : A) ->
      TendstoNat space
        (\ n -> function (approximants n) x)
        (f x)

record SemilatticeSup (I : Set) : Set1 where
  field
    leI :
      I -> I -> Set
    supI :
      I -> I -> I
    order-reflexiveI :
      (i : I) ->
      leI i i
    order-transitiveI :
      (i j k : I) ->
      leI i j ->
      leI j k ->
      leI i k
    order-antisymmetricI :
      (i j : I) ->
      leI i j ->
      leI j i ->
      i == j
    le-sup-leftI :
      (i j : I) ->
      leI i (supI i j)
    le-sup-rightI :
      (i j : I) ->
      leI j (supI i j)
    sup-leastI :
      (i j k : I) ->
      leI i k ->
      leI j k ->
      leI (supI i j) k

open SemilatticeSup

record Countable (I : Set) : Set1 where
  field
    code :
      I -> Nat
    code-injective :
      (i j : I) ->
      code i == code j ->
      i == j

TendstoAtTop :
  {I R M E : Set} ->
  {reals : CompleteOrderedField R} ->
  {extended : ExtendedNonnegativeReals R M reals} ->
  SemilatticeSup I ->
  PseudoEMetricSpace E reals extended ->
  (I -> E) ->
  E ->
  Set
TendstoAtTop {I = I} {R = R}
  {reals = reals} {extended = extended}
  index space sequence limit =
  (epsilon : R) ->
  (epsilon-positive : PositiveR reals epsilon) ->
  Exists I
    (\ cutoff ->
      (i : I) ->
      leI index cutoff i ->
      StrictLessM extended
        (edistance space (sequence i) limit)
        (finiteM extended epsilon (Both.first epsilon-positive)))

TendstoUniformlyOn :
  {A I R M E : Set} ->
  {reals : CompleteOrderedField R} ->
  {extended : ExtendedNonnegativeReals R M reals} ->
  SemilatticeSup I ->
  PseudoEMetricSpace E reals extended ->
  (I -> A -> E) ->
  (A -> E) ->
  Predicate A ->
  Set
TendstoUniformlyOn {A = A} {I = I} {R = R}
  {reals = reals} {extended = extended}
  index space functions limit S =
  (epsilon : R) ->
  (epsilon-positive : PositiveR reals epsilon) ->
  Exists I
    (\ cutoff ->
      (i : I) ->
      leI index cutoff i ->
      (x : A) ->
      S x ->
      StrictLessM extended
        (edistance space (functions i x) (limit x))
        (finiteM extended epsilon (Both.first epsilon-positive)))

egorov-s-theorem : Set2
egorov-s-theorem =
  (A I R M E : Set) ->
  (reals : CompleteOrderedField R) ->
  RealNumberPresentation reals ->
  (extended : ExtendedNonnegativeReals R M reals) ->
  ENNRealPresentation extended ->
  (events : SigmaAlgebra A) ->
  (measure : Measure extended events) ->
  (space : PseudoEMetricSpace E reals extended) ->
  (index : SemilatticeSup I) ->
  I ->
  Countable I ->
  (functions : I -> A -> E) ->
  (limit : A -> E) ->
  ((i : I) -> StronglyMeasurable reals events space (functions i)) ->
  StronglyMeasurable reals events space limit ->
  (S : Predicate A) ->
  measurable events S ->
  outerMass measure S != infinityM extended ->
  AlmostEverywhere measure
    (\ x ->
      S x ->
      TendstoAtTop index space
        (\ i -> functions i x)
        (limit x)) ->
  (epsilon : R) ->
  (epsilon-positive : PositiveR reals epsilon) ->
  ExistsL (Predicate A)
    (\ T ->
      BothL
        (Subset T S)
        (BothL
          (measurable events T)
          (BothL
            (lessOrEqualM extended
              (outerMass measure T)
              (finiteM extended epsilon (Both.first epsilon-positive)))
            (TendstoUniformlyOn index space functions limit
              (difference S T)))))
