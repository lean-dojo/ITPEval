-- Statement-only formalization of thousand-theorems corpus artifact Q7249519,
-- "Prokhorov's theorem": on a Hausdorff Borel space, finite measures with
-- bounded total mass and tails tending uniformly to zero outside compact sets
-- form a compact family in the weak topology, assuming normality or monotonicity
-- of the compact sets. This file contains no proof.

{-# OPTIONS --safe #-}

module Q7249519_prokhorov_s_theorem where

open import Agda.Primitive using (Level; lzero; lsuc; _⊔_; Setω)
open import Agda.Builtin.Equality renaming (_≡_ to _==_)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc)

data Bottom {a : Level} : Set a where

record Top {a : Level} : Set a where
  constructor top

Not :
  {a : Level} ->
  Set a ->
  Set a
Not {a} A =
  A -> Bottom {a}

record Both
  {a b : Level}
  (A : Set a)
  (B : Set b) :
  Set (a ⊔ b) where

  constructor both
  field
    first  : A
    second : B

data Either
  {a b : Level}
  (A : Set a)
  (B : Set b) :
  Set (a ⊔ b) where

  left  : A -> Either A B
  right : B -> Either A B

record Iff
  {a b : Level}
  (A : Set a)
  (B : Set b) :
  Set (a ⊔ b) where

  constructor equivalence
  field
    forward  : A -> B
    backward : B -> A

record Exists
  {a b : Level}
  (A : Set a)
  (P : A -> Set b) :
  Set (a ⊔ b) where

  constructor witness
  field
    value    : A
    property : P value

record Lift
  {a p : Level}
  (A : Set a) :
  Set (a ⊔ p) where

  constructor lifted
  field
    lower : A

infix 4 _!=_ _<=N_

_!=_ :
  {a : Level} ->
  {A : Set a} ->
  A ->
  A ->
  Set a
x != y =
  Not (x == y)

data _<=N_ : Nat -> Nat -> Set where
  zero<=   : {n : Nat} -> zero <=N n
  suc<=suc : {m n : Nat} -> m <=N n -> suc m <=N suc n

Predicate :
  {a : Level} ->
  Set a ->
  Set (lsuc a)
Predicate {a} A =
  A -> Set a

Family :
  {a : Level} ->
  Set a ->
  Set (lsuc a)
Family {a} A =
  Predicate A -> Set a

Empty :
  {a : Level} ->
  {A : Set a} ->
  Predicate A
Empty {a} _ =
  Bottom {a}

Whole :
  {a : Level} ->
  {A : Set a} ->
  Predicate A
Whole {a} _ =
  Top {a}

Complement :
  {a : Level} ->
  {A : Set a} ->
  Predicate A ->
  Predicate A
Complement P x =
  Not (P x)

Intersection :
  {a : Level} ->
  {A : Set a} ->
  Predicate A ->
  Predicate A ->
  Predicate A
Intersection P Q x =
  Both (P x) (Q x)

CountableUnion :
  {a : Level} ->
  {A : Set a} ->
  (Nat -> Predicate A) ->
  Predicate A
CountableUnion sets x =
  Exists Nat (\ n -> sets n x)

Subset :
  {a : Level} ->
  {A : Set a} ->
  Predicate A ->
  Predicate A ->
  Set a
Subset {A = A} P Q =
  (x : A) -> P x -> Q x

SamePredicate :
  {a : Level} ->
  {A : Set a} ->
  Predicate A ->
  Predicate A ->
  Set a
SamePredicate {A = A} P Q =
  (x : A) -> Iff (P x) (Q x)

Disjoint :
  {a : Level} ->
  {A : Set a} ->
  Predicate A ->
  Predicate A ->
  Set a
Disjoint {a} {A} P Q =
  (x : A) -> P x -> Q x -> Bottom {a}

Preimage :
  {A B : Set} ->
  (A -> B) ->
  Predicate B ->
  Predicate A
Preimage f U x =
  U (f x)

data Member
  {a : Level}
  {A : Set a}
  (x : A) :
  List A ->
  Set a where

  at-head :
    {xs : List A} ->
    Member x (x ∷ xs)

  in-tail :
    {y : A} ->
    {xs : List A} ->
    Member x xs ->
    Member x (y ∷ xs)

All :
  {a : Level} ->
  {A : Set a} ->
  (A -> Set a) ->
  List A ->
  Set a
All P [] =
  Top
All P (x ∷ xs) =
  Both (P x) (All P xs)

record TopologicalSpace
  {a : Level}
  (A : Set a) :
  Set (lsuc a) where

  field
    interior :
      Predicate A ->
      Predicate A

    interior-subset :
      (U : Predicate A) ->
      Subset (interior U) U

    interior-monotone :
      (U V : Predicate A) ->
      Subset U V ->
      Subset (interior U) (interior V)

    interior-open :
      (U : Predicate A) ->
      Subset (interior U) (interior (interior U))

    interior-whole :
      Subset Whole (interior Whole)

    interior-intersection :
      (U V : Predicate A) ->
      SamePredicate
        (interior (Intersection U V))
        (Intersection (interior U) (interior V))

open TopologicalSpace

IsOpen :
  {a : Level} ->
  {A : Set a} ->
  TopologicalSpace A ->
  Predicate A ->
  Set a
IsOpen topology U =
  Subset U (interior topology U)

IsClosed :
  {a : Level} ->
  {A : Set a} ->
  TopologicalSpace A ->
  Predicate A ->
  Set a
IsClosed topology U =
  IsOpen topology (Complement U)

record CoverWitness
  {a : Level}
  {A : Set a}
  (cover : Family A)
  (x : A) :
  Set (lsuc a) where

  field
    member-set      : Predicate A
    member-selected : cover member-set
    member-contains : member-set x

record FiniteSubcover
  {a : Level}
  {A : Set a}
  (target : Predicate A)
  (cover : Family A) :
  Set (lsuc a) where

  field
    selected :
      List (Predicate A)

    selected-from-cover :
      (U : Predicate A) ->
      Member U selected ->
      cover U

    selected-covers :
      (x : A) ->
      target x ->
      Exists (Predicate A)
        (\ U -> Both (Member U selected) (U x))

CompactFor :
  {a o : Level} ->
  {A : Set a} ->
  (Predicate A -> Set o) ->
  Predicate A ->
  Set (lsuc a ⊔ o)
CompactFor {A = A} Open target =
  (cover : Family A) ->
  ((U : Predicate A) -> cover U -> Open U) ->
  ((x : A) -> target x -> CoverWitness cover x) ->
  FiniteSubcover target cover

Compact :
  {a : Level} ->
  {A : Set a} ->
  TopologicalSpace A ->
  Predicate A ->
  Set (lsuc a)
Compact topology =
  CompactFor (IsOpen topology)

record T2Separation
  {a : Level}
  {A : Set a}
  (topology : TopologicalSpace A)
  (x y : A) :
  Set (lsuc a) where

  field
    left-neighborhood  : Predicate A
    right-neighborhood : Predicate A
    left-open          : IsOpen topology left-neighborhood
    right-open         : IsOpen topology right-neighborhood
    left-contains      : left-neighborhood x
    right-contains     : right-neighborhood y
    neighborhoods-disjoint :
      Disjoint left-neighborhood right-neighborhood

T2Space :
  {a : Level} ->
  {A : Set a} ->
  TopologicalSpace A ->
  Set (lsuc a)
T2Space {A = A} topology =
  (x y : A) ->
  x != y ->
  T2Separation topology x y

record NormalSeparation
  {a : Level}
  {A : Set a}
  (topology : TopologicalSpace A)
  (C D : Predicate A) :
  Set (lsuc a) where

  field
    left-open-set  : Predicate A
    right-open-set : Predicate A
    left-open      : IsOpen topology left-open-set
    right-open     : IsOpen topology right-open-set
    left-contained : Subset C left-open-set
    right-contained : Subset D right-open-set
    open-sets-disjoint :
      Disjoint left-open-set right-open-set

NormalSpace :
  {a : Level} ->
  {A : Set a} ->
  TopologicalSpace A ->
  Set (lsuc a)
NormalSpace {A = A} topology =
  (C D : Predicate A) ->
  IsClosed topology C ->
  IsClosed topology D ->
  Disjoint C D ->
  NormalSeparation topology C D

record SigmaAlgebra
  {a : Level}
  (A : Set a) :
  Set (lsuc a) where

  field
    measurable :
      Predicate A ->
      Set a

    measurable-empty :
      measurable Empty

    measurable-complement :
      (S : Predicate A) ->
      measurable S ->
      measurable (Complement S)

    measurable-countable-union :
      (sets : Nat -> Predicate A) ->
      ((n : Nat) -> measurable (sets n)) ->
      measurable (CountableUnion sets)

    measurable-congruent :
      (S T : Predicate A) ->
      SamePredicate S T ->
      measurable S ->
      measurable T

open SigmaAlgebra

data BorelGenerated
  {a : Level}
  {A : Set a}
  (topology : TopologicalSpace A) :
  Predicate A ->
  Set (lsuc a) where

  borel-open :
    {U : Predicate A} ->
    IsOpen topology U ->
    BorelGenerated topology U

  borel-empty :
    BorelGenerated topology Empty

  borel-complement :
    {S : Predicate A} ->
    BorelGenerated topology S ->
    BorelGenerated topology (Complement S)

  borel-countable-union :
    (sets : Nat -> Predicate A) ->
    ((n : Nat) -> BorelGenerated topology (sets n)) ->
    BorelGenerated topology (CountableUnion sets)

  borel-congruent :
    {S T : Predicate A} ->
    SamePredicate S T ->
    BorelGenerated topology S ->
    BorelGenerated topology T

record BorelSpace
  {a : Level}
  {A : Set a}
  (topology : TopologicalSpace A)
  (events : SigmaAlgebra A) :
  Set (lsuc (lsuc a)) where

  field
    borel-measurable :
      (S : Predicate A) ->
      BorelGenerated topology S ->
      measurable events S

    measurable-borel :
      (S : Predicate A) ->
      measurable events S ->
      BorelGenerated topology S

record CompleteOrderedField (R : Set) : Set1 where

  field
    zeroR oneR :
      R

    addR multiplyR :
      R -> R -> R

    negateR reciprocalR absoluteR :
      R -> R

    lessOrEqualR :
      R -> R -> Set

    fromNatR :
      Nat -> R

    one-not-zero :
      oneR != zeroR

    add-commutative :
      (x y : R) ->
      addR x y == addR y x

    add-associative :
      (x y z : R) ->
      addR (addR x y) z == addR x (addR y z)

    add-zero :
      (x : R) ->
      addR x zeroR == x

    add-inverse :
      (x : R) ->
      addR x (negateR x) == zeroR

    multiply-commutative :
      (x y : R) ->
      multiplyR x y == multiplyR y x

    multiply-associative :
      (x y z : R) ->
      multiplyR (multiplyR x y) z == multiplyR x (multiplyR y z)

    multiply-one :
      (x : R) ->
      multiplyR x oneR == x

    distribute :
      (x y z : R) ->
      multiplyR x (addR y z) ==
      addR (multiplyR x y) (multiplyR x z)

    multiply-reciprocal :
      (x : R) ->
      x != zeroR ->
      multiplyR x (reciprocalR x) == oneR

    order-reflexive :
      (x : R) ->
      lessOrEqualR x x

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
      (x y : R) ->
      Either (lessOrEqualR x y) (lessOrEqualR y x)

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
      (x : R) ->
      lessOrEqualR zeroR (absoluteR x)

    absolute-of-nonnegative :
      (x : R) ->
      lessOrEqualR zeroR x ->
      absoluteR x == x

    absolute-of-nonpositive :
      (x : R) ->
      lessOrEqualR x zeroR ->
      absoluteR x == negateR x

    absolute-zero-only :
      (x : R) ->
      absoluteR x == zeroR ->
      x == zeroR

    absolute-add :
      (x y : R) ->
      lessOrEqualR
        (absoluteR (addR x y))
        (addR (absoluteR x) (absoluteR y))

    absolute-multiply :
      (x y : R) ->
      absoluteR (multiplyR x y) ==
      multiplyR (absoluteR x) (absoluteR y)

    fromNat-zero :
      fromNatR zero == zeroR

    fromNat-successor :
      (n : Nat) ->
      fromNatR (suc n) == addR (fromNatR n) oneR

    archimedean :
      (x : R) ->
      Exists Nat (\ n -> lessOrEqualR x (fromNatR n))

    least-upper-bound :
      (P : Predicate R) ->
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

subtractR :
  {R : Set} ->
  CompleteOrderedField R ->
  R -> R -> R
subtractR reals x y =
  addR reals x (negateR reals y)

StrictLess :
  {R : Set} ->
  CompleteOrderedField R ->
  R -> R -> Set
StrictLess reals x y =
  Both (lessOrEqualR reals x y) (x != y)

Positive :
  {R : Set} ->
  CompleteOrderedField R ->
  R -> Set
Positive reals x =
  StrictLess reals (zeroR reals) x

record Nonnegative
  {R : Set}
  (reals : CompleteOrderedField R) :
  Set where

  constructor nonnegative
  field
    value       : R
    value-is-nonnegative :
      lessOrEqualR reals (zeroR reals) value

open Nonnegative

RealOpen :
  {R : Set} ->
  CompleteOrderedField R ->
  Predicate R ->
  Set
RealOpen {R} reals U =
  (x : R) ->
  U x ->
  Exists R
    (\ radius ->
      Both
        (Positive reals radius)
        ((y : R) ->
          StrictLess reals
            (absoluteR reals (subtractR reals y x))
            radius ->
          U y))

ContinuousReal :
  {R E : Set} ->
  CompleteOrderedField R ->
  TopologicalSpace E ->
  (E -> R) ->
  Set1
ContinuousReal reals topology f =
  (U : Predicate _) ->
  RealOpen reals U ->
  IsOpen topology (Preimage f U)

Bounded :
  {R E : Set} ->
  CompleteOrderedField R ->
  (E -> R) ->
  Set
Bounded {R} {E} reals f =
  Exists R
    (\ bound ->
      Both
        (lessOrEqualR reals (zeroR reals) bound)
        ((x : E) ->
          lessOrEqualR reals (absoluteR reals (f x)) bound))

record BoundedContinuous
  {R E : Set}
  (reals : CompleteOrderedField R)
  (topology : TopologicalSpace E)
  (f : E -> R) :
  Set1 where

  field
    bounded    : Bounded reals f
    continuous : ContinuousReal reals topology f

PairwiseDisjoint :
  {a : Level} ->
  {A : Set a} ->
  (Nat -> Predicate A) ->
  Set a
PairwiseDisjoint {a} {A} sets =
  (i j : Nat) ->
  i != j ->
  Disjoint (sets i) (sets j)

sumFirst :
  {R : Set} ->
  CompleteOrderedField R ->
  (Nat -> R) ->
  Nat ->
  R
sumFirst reals terms zero =
  zeroR reals
sumFirst reals terms (suc n) =
  addR reals (sumFirst reals terms n) (terms n)

SequentialLimit :
  {R : Set} ->
  CompleteOrderedField R ->
  (Nat -> R) ->
  R ->
  Set
SequentialLimit reals sequence limit =
  (epsilon : _) ->
  Positive reals epsilon ->
  Exists Nat
    (\ cutoff ->
      (n : Nat) ->
      cutoff <=N n ->
      StrictLess reals
        (absoluteR reals
          (subtractR reals (sequence n) limit))
        epsilon)

record IsInfimumLarge
  {R : Set}
  (reals : CompleteOrderedField R)
  (P : R -> Set1)
  (bound : R) :
  Set1 where

  field
    lower-bound :
      (x : R) ->
      P x ->
      lessOrEqualR reals bound x

    greatest-lower-bound :
      (lower : R) ->
      ((x : R) -> P x -> lessOrEqualR reals lower x) ->
      lessOrEqualR reals lower bound

record IsSupremumLarge
  {R : Set}
  (reals : CompleteOrderedField R)
  (P : R -> Set1)
  (bound : R) :
  Set1 where

  field
    upper-bound :
      (x : R) ->
      P x ->
      lessOrEqualR reals x bound

    least-upper-bound-large :
      (upper : R) ->
      ((x : R) -> P x -> lessOrEqualR reals x upper) ->
      lessOrEqualR reals bound upper

record FiniteMeasure
  {R E : Set}
  (reals : CompleteOrderedField R)
  (events : SigmaAlgebra E) :
  Set1 where

  field
    mass :
      Predicate E ->
      R

    mass-congruent :
      (S T : Predicate E) ->
      SamePredicate S T ->
      mass S == mass T

    mass-empty :
      mass Empty == zeroR reals

    mass-nonnegative :
      (S : Predicate E) ->
      lessOrEqualR reals (zeroR reals) (mass S)

    mass-monotone :
      (S T : Predicate E) ->
      Subset S T ->
      lessOrEqualR reals (mass S) (mass T)

    mass-trimmed :
      (S : Predicate E) ->
      IsInfimumLarge reals
        (\ candidate ->
          Exists (Predicate E)
            (\ T ->
              Both
                (measurable events T)
                (Both
                  (Subset S T)
                  (candidate == mass T))))
        (mass S)

    measurable-countable-additivity :
      (sets : Nat -> Predicate E) ->
      ((n : Nat) -> measurable events (sets n)) ->
      PairwiseDisjoint sets ->
      SequentialLimit reals
        (\ count ->
          sumFirst reals (\ n -> mass (sets n)) count)
        (mass (CountableUnion sets))

open FiniteMeasure

record SimpleFunctionBelow
  {R E : Set}
  (reals : CompleteOrderedField R)
  (events : SigmaAlgebra E)
  (f : E -> R) :
  Set1 where

  field
    cutoff :
      Nat

    index :
      E -> Nat

    values :
      Nat -> R

    index-within :
      (x : E) ->
      index x <=N cutoff

    measurable-fibers :
      (n : Nat) ->
      measurable events (\ x -> index x == n)

    values-nonnegative :
      (n : Nat) ->
      lessOrEqualR reals (zeroR reals) (values n)

    pointwise-below :
      (x : E) ->
      lessOrEqualR reals (values (index x)) (f x)

open SimpleFunctionBelow

simpleIntegral :
  {R E : Set} ->
  {reals : CompleteOrderedField R} ->
  {events : SigmaAlgebra E} ->
  (measure : FiniteMeasure reals events) ->
  {f : E -> R} ->
  SimpleFunctionBelow reals events f ->
  R
simpleIntegral {reals = reals} measure simple =
  sumFirst reals
    (\ n ->
      multiplyR reals
        (values simple n)
        (mass measure (\ x -> index simple x == n)))
    (suc (cutoff simple))

SimpleIntegralCandidate :
  {R E : Set} ->
  {reals : CompleteOrderedField R} ->
  {events : SigmaAlgebra E} ->
  FiniteMeasure reals events ->
  (E -> R) ->
  R ->
  Set1
SimpleIntegralCandidate {reals = reals} {events = events}
    measure f candidate =
  Exists (SimpleFunctionBelow reals events f)
    (\ simple -> candidate == simpleIntegral measure simple)

LowerIntegralValue :
  {R E : Set} ->
  {reals : CompleteOrderedField R} ->
  {events : SigmaAlgebra E} ->
  FiniteMeasure reals events ->
  (E -> R) ->
  R ->
  Set1
LowerIntegralValue {reals = reals} measure f value =
  IsSupremumLarge reals
    (SimpleIntegralCandidate measure f)
    value

record JordanParts
  {R E : Set}
  (reals : CompleteOrderedField R)
  (f positivePart negativePart : E -> R) :
  Set1 where

  field
    positive-nonnegative :
      (x : E) ->
      lessOrEqualR reals (zeroR reals) (positivePart x)

    negative-nonnegative :
      (x : E) ->
      lessOrEqualR reals (zeroR reals) (negativePart x)

    reconstructs :
      (x : E) ->
      f x ==
      subtractR reals (positivePart x) (negativePart x)

    disjoint-parts :
      (x : E) ->
      Either
        (positivePart x == zeroR reals)
        (negativePart x == zeroR reals)

IntegralValue :
  {R E : Set} ->
  {reals : CompleteOrderedField R} ->
  {events : SigmaAlgebra E} ->
  FiniteMeasure reals events ->
  (E -> R) ->
  R ->
  Set1
IntegralValue {R} {E} {reals} {events} measure f value =
  Exists (E -> R)
    (\ positivePart ->
      Exists (E -> R)
        (\ negativePart ->
          Both
            (JordanParts reals f positivePart negativePart)
            (Exists R
              (\ positiveIntegral ->
                Exists R
                  (\ negativeIntegral ->
                    Both
                      (LowerIntegralValue
                        measure positivePart positiveIntegral)
                      (Both
                        (LowerIntegralValue
                          measure negativePart negativeIntegral)
                        (value ==
                          subtractR reals
                            positiveIntegral negativeIntegral)))))))

IntegralPreimage :
  {R E : Set} ->
  {reals : CompleteOrderedField R} ->
  {events : SigmaAlgebra E} ->
  (f : E -> R) ->
  Predicate R ->
  Predicate (FiniteMeasure reals events)
IntegralPreimage f U measure =
  Exists _
    (\ integral ->
      Both
        (IntegralValue measure f integral)
        (U integral))

record WeakConstraint
  {R E : Set}
  (reals : CompleteOrderedField R)
  (topology : TopologicalSpace E)
  : Set1 where

  field
    test-function :
      E -> R

    test-bounded-continuous :
      BoundedContinuous reals topology test-function

    real-region :
      Predicate R

    real-region-open :
      RealOpen reals real-region

open WeakConstraint

SatisfiesConstraint :
  {R E : Set} ->
  {reals : CompleteOrderedField R} ->
  {topology : TopologicalSpace E} ->
  {events : SigmaAlgebra E} ->
  FiniteMeasure reals events ->
  WeakConstraint reals topology ->
  Set1
SatisfiesConstraint measure constraint =
  IntegralPreimage
    (test-function constraint)
    (real-region constraint)
    measure

BasicWeakOpen :
  {R E : Set} ->
  {reals : CompleteOrderedField R} ->
  {topology : TopologicalSpace E} ->
  {events : SigmaAlgebra E} ->
  List (WeakConstraint reals topology) ->
  Predicate (FiniteMeasure reals events)
BasicWeakOpen constraints measure =
  All (SatisfiesConstraint measure) constraints

-- This is the topology generated by the integral subbasis: a set is weakly
-- open exactly when each of its points has a finite intersection of subbasic
-- bounded-continuous integral neighborhoods contained in the set.
WeakOpen :
  {R E : Set} ->
  (reals : CompleteOrderedField R) ->
  (topology : TopologicalSpace E) ->
  (events : SigmaAlgebra E) ->
  Predicate (FiniteMeasure reals events) ->
  Set1
WeakOpen reals topology events U =
  (measure : FiniteMeasure reals events) ->
  U measure ->
  Exists (List (WeakConstraint reals topology))
    (\ constraints ->
      Both
        (BasicWeakOpen {events = events} constraints measure)
        (Subset (BasicWeakOpen {events = events} constraints) U))

TendsToZero :
  {R : Set} ->
  (reals : CompleteOrderedField R) ->
  (Nat -> Nonnegative reals) ->
  Set
TendsToZero reals u =
  (epsilon : _) ->
  Positive reals epsilon ->
  Exists Nat
    (\ cutoff ->
      (n : Nat) ->
      cutoff <=N n ->
      StrictLess reals (value (u n)) epsilon)

Monotone :
  {a : Level} ->
  {A : Set a} ->
  (Nat -> Predicate A) ->
  Set a
Monotone sets =
  (m n : Nat) ->
  m <=N n ->
  Subset (sets m) (sets n)

ProkhorovFamily :
  {R E : Set} ->
  {reals : CompleteOrderedField R} ->
  {events : SigmaAlgebra E} ->
  (u : Nat -> Nonnegative reals) ->
  (K : Nat -> Predicate E) ->
  Nonnegative reals ->
  Predicate (FiniteMeasure reals events)
ProkhorovFamily {reals = reals} u K C measure =
  Lift {p = lsuc lzero}
    (Both
      (lessOrEqualR reals
        (mass measure Whole)
        (value C))
      ((n : Nat) ->
        lessOrEqualR reals
          (mass measure (Complement (K n)))
          (value (u n))))

prokhorov-s-theorem : Set2
prokhorov-s-theorem =
  (R E : Set) ->
  (reals : CompleteOrderedField R) ->
  (topology : TopologicalSpace E) ->
  T2Space topology ->
  (events : SigmaAlgebra E) ->
  BorelSpace topology events ->
  (u : Nat -> Nonnegative reals) ->
  (K : Nat -> Predicate E) ->
  (C : Nonnegative reals) ->
  TendsToZero reals u ->
  ((n : Nat) -> Compact topology (K n)) ->
  Either (NormalSpace topology) (Monotone K) ->
  CompactFor
    (WeakOpen reals topology events)
    (ProkhorovFamily u K C)
