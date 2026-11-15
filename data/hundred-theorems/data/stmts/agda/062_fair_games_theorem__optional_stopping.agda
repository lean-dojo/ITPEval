-- Statement-only formalization of Hundred Theorems artifact 062,
-- "Fair Games Theorem (Optional Stopping)": the characterization of real-valued
-- discrete-time submartingales by monotonicity of expectations between ordered
-- bounded stopping times. This file contains no proof.

module FairGamesOptionalStopping where

open import Agda.Primitive using (Level; lsuc; _⊔_)
open import Agda.Builtin.Equality renaming (_≡_ to _==_)
open import Agda.Builtin.Nat using (Nat; zero; suc)

infix 4 _!=_ _<=N_ _<=T_

data Bottom {ℓ : Level} : Set ℓ where

Not : {ℓ : Level} -> Set ℓ -> Set ℓ
Not {ℓ} A = A -> Bottom {ℓ}

_!=_ : {ℓ : Level} {A : Set ℓ} -> A -> A -> Set ℓ
x != y = Not (x == y)

record Top {ℓ : Level} : Set ℓ where
  constructor top

record Both {ℓ₁ ℓ₂ : Level}
  (A : Set ℓ₁) (B : Set ℓ₂) : Set (ℓ₁ ⊔ ℓ₂) where
  constructor both
  field
    first  : A
    second : B

data Either {ℓ₁ ℓ₂ : Level}
  (A : Set ℓ₁) (B : Set ℓ₂) : Set (ℓ₁ ⊔ ℓ₂) where
  left  : A -> Either A B
  right : B -> Either A B

record Iff {ℓ₁ ℓ₂ : Level}
  (A : Set ℓ₁) (B : Set ℓ₂) : Set (ℓ₁ ⊔ ℓ₂) where
  constructor equivalence
  field
    forward  : A -> B
    backward : B -> A

record Exists {ℓ₁ ℓ₂ : Level}
  (A : Set ℓ₁) (P : A -> Set ℓ₂) : Set (ℓ₁ ⊔ ℓ₂) where
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

StrictLess :
  {R : Set} ->
  CompleteOrderedField R ->
  R ->
  R ->
  Set
StrictLess reals x y =
  Both (lessOrEqual reals x y) (x != y)

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

subtract :
  {R : Set} ->
  CompleteOrderedField R ->
  R ->
  R ->
  R
subtract reals x y =
  add reals x (negate reals y)

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
        (absoluteValue reals
          (subtract reals (sequence n) limit))
        epsilon)

data ExtendedNonnegative (R : Set) : Set where
  finiteValue   : R -> ExtendedNonnegative R
  infiniteValue : ExtendedNonnegative R

addExtended :
  {R : Set} ->
  CompleteOrderedField R ->
  ExtendedNonnegative R ->
  ExtendedNonnegative R ->
  ExtendedNonnegative R
addExtended reals (finiteValue x) (finiteValue y) =
  finiteValue (add reals x y)
addExtended reals infiniteValue _ =
  infiniteValue
addExtended reals _ infiniteValue =
  infiniteValue

partialExtendedSum :
  {R : Set} ->
  CompleteOrderedField R ->
  (Nat -> ExtendedNonnegative R) ->
  Nat ->
  ExtendedNonnegative R
partialExtendedSum reals sequence zero =
  finiteValue (zeroR reals)
partialExtendedSum reals sequence (suc n) =
  addExtended reals
    (partialExtendedSum reals sequence n)
    (sequence n)

StrictBelowExtended :
  {R : Set} ->
  CompleteOrderedField R ->
  R ->
  ExtendedNonnegative R ->
  Set
StrictBelowExtended reals bound (finiteValue value) =
  StrictLess reals bound value
StrictBelowExtended reals bound infiniteValue =
  Top

ExtendedLimit :
  {R : Set} ->
  CompleteOrderedField R ->
  (Nat -> ExtendedNonnegative R) ->
  ExtendedNonnegative R ->
  Set
ExtendedLimit reals sequence (finiteValue limit) =
  Exists (Nat -> _)
    (\ values ->
      Both
        ((n : Nat) -> sequence n == finiteValue (values n))
        (SequentialLimit reals values limit))
ExtendedLimit reals sequence infiniteValue =
  (bound : _) ->
  Exists Nat
    (\ n -> StrictBelowExtended reals bound (sequence n))

Disjoint :
  {A : Set} ->
  Predicate A ->
  Predicate A ->
  Set
Disjoint E F =
  (x : _) -> Not (Both (E x) (F x))

PairwiseDisjoint :
  {A : Set} ->
  (Nat -> Predicate A) ->
  Set
PairwiseDisjoint sets =
  (m n : Nat) -> m != n -> Disjoint (sets m) (sets n)

record CountablyAdditiveMeasure
  {R A : Set}
  (analysis : StandardRealAnalysis R)
  (events : SigmaAlgebra A) : Set1 where
  field
    measureValue : Predicate A -> ExtendedNonnegative R

    measure-nonnegative :
      (E : Predicate A) ->
      (value : R) ->
      measureValue E == finiteValue value ->
      lessOrEqual (algebra analysis)
        (zeroR (algebra analysis))
        value
    measure-empty :
      measureValue emptySet ==
      finiteValue (zeroR (algebra analysis))
    measure-congruent :
      (E F : Predicate A) ->
      ((x : A) -> Iff (E x) (F x)) ->
      measureValue E == measureValue F
    measure-countably-additive :
      (sets : Nat -> Predicate A) ->
      ((n : Nat) -> measurable events (sets n)) ->
      PairwiseDisjoint sets ->
      ExtendedLimit
        (algebra analysis)
        (\ n ->
          partialExtendedSum
            (algebra analysis)
            (\ k -> measureValue (sets k))
            n)
        (measureValue (countableUnion sets))

open CountablyAdditiveMeasure

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

record MeasureIntegration
  {R A : Set}
  (analysis : StandardRealAnalysis R)
  (events : SigmaAlgebra A) : Set1 where
  field
    measure-structure : CountablyAdditiveMeasure analysis events
    integrable : (A -> R) -> Set
    integral : (A -> R) -> R
    indicator : Predicate A -> A -> R

    integrable-measurable :
      (f : A -> R) ->
      integrable f ->
      MeasurableFunction events (borel analysis) f
    integrable-congruent :
      (f g : A -> R) ->
      ((x : A) -> f x == g x) ->
      Iff (integrable f) (integrable g)
    integral-congruent :
      (f g : A -> R) ->
      integrable f ->
      integrable g ->
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
    integrable-absolute :
      (f : A -> R) ->
      integrable f ->
      integrable
        (\ x -> absoluteValue (algebra analysis) (f x))
    integrable-of-dominated :
      (f g : A -> R) ->
      MeasurableFunction events (borel analysis) f ->
      integrable g ->
      ((x : A) ->
        lessOrEqual (algebra analysis)
          (absoluteValue (algebra analysis) (f x))
          (g x)) ->
      integrable f
    integral-monotone :
      (f g : A -> R) ->
      integrable f ->
      integrable g ->
      ((x : A) ->
        lessOrEqual (algebra analysis) (f x) (g x)) ->
      lessOrEqual (algebra analysis) (integral f) (integral g)

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
    indicator-integrable-iff-finite :
      (E : Predicate A) ->
      measurable events E ->
      Iff
        (integrable (indicator E))
        (Exists R
          (\ value ->
            measureValue measure-structure E ==
            finiteValue value))
    integral-indicator :
      (E : Predicate A) ->
      measurable events E ->
      (value : R) ->
      measureValue measure-structure E == finiteValue value ->
      integral (indicator E) == value
    integrable-restrict :
      (f : A -> R) ->
      integrable f ->
      (E : Predicate A) ->
      measurable events E ->
      integrable
        (\ x ->
          multiply (algebra analysis)
            (indicator E x)
            (f x))

    -- Countable order-continuity distinguishes this Daniell-Lebesgue
    -- integral from a merely finitely additive positive functional.
    monotone-convergence :
      (sequence : Nat -> A -> R) ->
      (limit : A -> R) ->
      ((n : Nat) -> integrable (sequence n)) ->
      integrable limit ->
      ((n : Nat) ->
        (x : A) ->
        lessOrEqual (algebra analysis)
          (zeroR (algebra analysis))
          (sequence n x)) ->
      ((n : Nat) ->
        (x : A) ->
        lessOrEqual (algebra analysis)
          (sequence n x)
          (sequence (suc n) x)) ->
      ((x : A) ->
        SequentialLimit
          (algebra analysis)
          (\ n -> sequence n x)
          (limit x)) ->
      SequentialLimit
        (algebra analysis)
        (\ n -> integral (sequence n))
        (integral limit)

open MeasureIntegration

setIntegral :
  {R A : Set}
  {analysis : StandardRealAnalysis R}
  {events : SigmaAlgebra A} ->
  MeasureIntegration analysis events ->
  (A -> R) ->
  Predicate A ->
  R
setIntegral {analysis = analysis} integration f E =
  integral integration
    (\ x ->
      multiply (algebra analysis)
        (indicator integration E x)
        (f x))

IsSubalgebra :
  {A : Set} ->
  SigmaAlgebra A ->
  SigmaAlgebra A ->
  Set1
IsSubalgebra smaller larger =
  (E : Predicate _) ->
  measurable smaller E ->
  measurable larger E

record IsFiltration
  {A : Set}
  (base : SigmaAlgebra A)
  (filtration : Nat -> SigmaAlgebra A) : Set1 where
  field
    contained-in-base :
      (n : Nat) ->
      IsSubalgebra (filtration n) base
    increasing :
      (m n : Nat) ->
      m <=N n ->
      IsSubalgebra (filtration m) (filtration n)

record SigmaFinite
  {R A : Set}
  {analysis : StandardRealAnalysis R}
  {base : SigmaAlgebra A}
  (integration : MeasureIntegration analysis base)
  (events : SigmaAlgebra A) : Set1 where
  field
    events-contained-in-base :
      IsSubalgebra events base
    pieces : Nat -> Predicate A
    pieces-measurable :
      (n : Nat) -> measurable events (pieces n)
    pieces-finite-measure :
      (n : Nat) ->
      Exists R
        (\ value ->
          measureValue
            (measure-structure integration)
            (pieces n) ==
          finiteValue value)
    pieces-cover :
      (x : A) -> Exists Nat (\ n -> pieces n x)

SigmaFiniteFiltration :
  {R A : Set}
  {analysis : StandardRealAnalysis R}
  {base : SigmaAlgebra A} ->
  MeasureIntegration analysis base ->
  (Nat -> SigmaAlgebra A) ->
  Set1
SigmaFiniteFiltration integration filtration =
  (n : Nat) -> SigmaFinite integration (filtration n)

data ExtendedNat : Set where
  finite   : Nat -> ExtendedNat
  infinity : ExtendedNat

_<=T_ : ExtendedNat -> ExtendedNat -> Set
finite m <=T finite n = m <=N n
finite m <=T infinity = Top
infinity <=T finite n = Bottom
infinity <=T infinity = Top

IsStoppingTime :
  {A : Set} ->
  (Nat -> SigmaAlgebra A) ->
  (A -> ExtendedNat) ->
  Set
IsStoppingTime filtration stoppingTime =
  (n : Nat) ->
  measurable (filtration n)
    (\ x -> stoppingTime x <=T finite n)

StoppingTimeOrder :
  {A : Set} ->
  (A -> ExtendedNat) ->
  (A -> ExtendedNat) ->
  Set
StoppingTimeOrder firstTime secondTime =
  (x : _) -> firstTime x <=T secondTime x

BoundedStoppingTime :
  {A : Set} ->
  (A -> ExtendedNat) ->
  Set
BoundedStoppingTime stoppingTime =
  Exists Nat
    (\ bound ->
      (x : _) -> stoppingTime x <=T finite bound)

stoppedValue :
  {R A : Set} ->
  StandardRealAnalysis R ->
  (Nat -> A -> R) ->
  (A -> ExtendedNat) ->
  A ->
  R
stoppedValue analysis process stoppingTime x with stoppingTime x
... | finite n = process n x
... | infinity = zeroR (algebra analysis)

StronglyAdapted :
  {R A : Set} ->
  StandardRealAnalysis R ->
  (Nat -> SigmaAlgebra A) ->
  (Nat -> A -> R) ->
  Set1
StronglyAdapted analysis filtration process =
  (n : Nat) ->
  MeasurableFunction
    (filtration n)
    (borel analysis)
    (process n)

ProcessIntegrable :
  {R A : Set}
  {analysis : StandardRealAnalysis R}
  {base : SigmaAlgebra A} ->
  MeasureIntegration analysis base ->
  (Nat -> A -> R) ->
  Set
ProcessIntegrable integration process =
  (n : Nat) -> integrable integration (process n)

record Submartingale
  {R A : Set}
  (analysis : StandardRealAnalysis R)
  (base : SigmaAlgebra A)
  (integration : MeasureIntegration analysis base)
  (filtration : Nat -> SigmaAlgebra A)
  (process : Nat -> A -> R) : Set1 where
  field
    strongly-adapted :
      StronglyAdapted analysis filtration process
    integrable-process :
      ProcessIntegrable integration process
    conditional-monotonicity :
      (m n : Nat) ->
      m <=N n ->
      (E : Predicate A) ->
      measurable (filtration m) E ->
      lessOrEqual (algebra analysis)
        (setIntegral integration (process m) E)
        (setIntegral integration (process n) E)

OptionalStoppingMonotonicity :
  {R A : Set} ->
  (analysis : StandardRealAnalysis R) ->
  (base : SigmaAlgebra A) ->
  (integration : MeasureIntegration analysis base) ->
  (filtration : Nat -> SigmaAlgebra A) ->
  (process : Nat -> A -> R) ->
  Set
OptionalStoppingMonotonicity {A = A}
  analysis base integration filtration process =
  (firstTime secondTime : A -> ExtendedNat) ->
  IsStoppingTime filtration firstTime ->
  IsStoppingTime filtration secondTime ->
  StoppingTimeOrder firstTime secondTime ->
  BoundedStoppingTime secondTime ->
  lessOrEqual (algebra analysis)
    (integral integration
      (stoppedValue analysis process firstTime))
    (integral integration
      (stoppedValue analysis process secondTime))

fair-games-theorem-optional-stopping : Set1
fair-games-theorem-optional-stopping =
  (R A : Set) ->
  (analysis : StandardRealAnalysis R) ->
  (base : SigmaAlgebra A) ->
  (integration : MeasureIntegration analysis base) ->
  (filtration : Nat -> SigmaAlgebra A) ->
  IsFiltration base filtration ->
  SigmaFiniteFiltration integration filtration ->
  (process : Nat -> A -> R) ->
  StronglyAdapted analysis filtration process ->
  ProcessIntegrable integration process ->
  Iff
    (Submartingale analysis base integration filtration process)
    (OptionalStoppingMonotonicity
      analysis base integration filtration process)
