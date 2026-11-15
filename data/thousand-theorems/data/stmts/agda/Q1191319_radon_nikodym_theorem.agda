-- Statement-only formalization of thousand-theorems corpus artifact Q1191319,
-- "Radon–Nikodym theorem": under a Lebesgue decomposition, absolute
-- continuity is equivalent to recovering a measure by weighting the reference
-- measure with its Radon-Nikodym derivative. This file contains no proof.

{-# OPTIONS --safe #-}

module Q1191319_radon_nikodym_theorem where

open import Agda.Primitive using (Level; lzero; lsuc; _⊔_)
open import Agda.Builtin.Equality renaming (_≡_ to _==_)
open import Agda.Builtin.Nat using (Nat; zero; suc)

data Bottom {a : Level} : Set a where

record Top {a : Level} : Set a where
  constructor top

Not :
  {a : Level} ->
  Set a ->
  Set a
Not {a} proposition =
  proposition -> Bottom {a}

record Both
  {a b : Level}
  (A : Set a)
  (B : Set b) :
  Set (a ⊔ b) where

  constructor both
  field
    first  : A
    second : B

record Iff
  {a b : Level}
  (A : Set a)
  (B : Set b) :
  Set (a ⊔ b) where

  constructor equivalence
  field
    forward  : A -> B
    backward : B -> A

data Either
  {a b : Level}
  (A : Set a)
  (B : Set b) :
  Set (a ⊔ b) where

  left  : A -> Either A B
  right : B -> Either A B

record Exists
  {a b : Level}
  (A : Set a)
  (P : A -> Set b) :
  Set (a ⊔ b) where

  constructor witness
  field
    value    : A
    property : P value

infix 4 _!=_ _<=N_ _<N_
infixl 6 _+N_
infixl 7 _*N_

_!=_ :
  {a : Level} ->
  {A : Set a} ->
  A ->
  A ->
  Set a
x != y =
  Not (x == y)

_+N_ : Nat -> Nat -> Nat
zero +N n =
  n
suc m +N n =
  suc (m +N n)

_*N_ : Nat -> Nat -> Nat
zero *N n =
  zero
suc m *N n =
  n +N (m *N n)

data _<=N_ : Nat -> Nat -> Set where
  zero<=   : {n : Nat} -> zero <=N n
  suc<=suc : {m n : Nat} -> m <=N n -> suc m <=N suc n

_<N_ : Nat -> Nat -> Set
m <N n =
  suc m <=N n

-- A rational is the integer positivePart - negativePart divided by
-- suc denominatorCode. Equality and order below quotient this presentation.
record Rational : Set where
  constructor rational
  field
    positivePart   : Nat
    negativePart   : Nat
    denominatorCode : Nat

open Rational

denominatorValue : Rational -> Nat
denominatorValue q =
  suc (denominatorCode q)

denominatorProductCode : Nat -> Nat -> Nat
denominatorProductCode d e =
  d +N (e +N (d *N e))

zeroQ : Rational
zeroQ =
  rational zero zero zero

addQ : Rational -> Rational -> Rational
addQ q r =
  rational
    ((positivePart q *N denominatorValue r) +N
     (positivePart r *N denominatorValue q))
    ((negativePart q *N denominatorValue r) +N
     (negativePart r *N denominatorValue q))
    (denominatorProductCode (denominatorCode q) (denominatorCode r))

multiplyQ : Rational -> Rational -> Rational
multiplyQ q r =
  rational
    ((positivePart q *N positivePart r) +N
     (negativePart q *N negativePart r))
    ((positivePart q *N negativePart r) +N
     (negativePart q *N positivePart r))
    (denominatorProductCode (denominatorCode q) (denominatorCode r))

RationalEqual : Rational -> Rational -> Set
RationalEqual q r =
  ((positivePart q *N denominatorValue r) +N
   (negativePart r *N denominatorValue q))
  ==
  ((positivePart r *N denominatorValue q) +N
   (negativePart q *N denominatorValue r))

RationalLE : Rational -> Rational -> Set
RationalLE q r =
  ((positivePart q *N denominatorValue r) +N
   (negativePart r *N denominatorValue q))
  <=N
  ((positivePart r *N denominatorValue q) +N
   (negativePart q *N denominatorValue r))

RationalLT : Rational -> Rational -> Set
RationalLT q r =
  ((positivePart q *N denominatorValue r) +N
   (negativePart r *N denominatorValue q))
  <N
  ((positivePart r *N denominatorValue q) +N
   (negativePart q *N denominatorValue r))

-- Reals are located lower Dedekind cuts of the concrete rationals.
record DedekindReal : Set1 where
  field
    lower :
      Rational ->
      Set

    lower-respects-rational-equality :
      (q r : Rational) ->
      RationalEqual q r ->
      Iff (lower q) (lower r)

    lower-inhabited :
      Exists Rational lower

    lower-proper :
      Exists Rational (\ q -> Not (lower q))

    lower-downward :
      (q r : Rational) ->
      RationalLT q r ->
      lower r ->
      lower q

    lower-rounded :
      (q : Rational) ->
      lower q ->
      Exists Rational
        (\ r -> Both (RationalLT q r) (lower r))

    lower-located :
      (q r : Rational) ->
      RationalLT q r ->
      Either (lower q) (Not (lower r))

open DedekindReal

record NonnegativeReal : Set1 where
  constructor nonnegative-real
  field
    real :
      DedekindReal

    nonnegative :
      (q : Rational) ->
      RationalLT q zeroQ ->
      lower real q

open NonnegativeReal

data ENNReal : Set1 where
  finite     : NonnegativeReal -> ENNReal
  infinity   : ENNReal
  sumENN     : ENNReal -> ENNReal -> ENNReal
  productENN : ENNReal -> ENNReal -> ENNReal

-- Every constructor is interpreted by its complete rational lower cut.
-- Product convolution is total: infinity times an extensionally zero value
-- has the zero cut without requiring a decision that the second value is zero.
ENNLower : ENNReal -> Rational -> Set
ENNLower (finite x) r =
  lower (real x) r
ENNLower infinity r =
  Top
ENNLower (sumENN x y) r =
  Exists Rational
    (\ p ->
      Exists Rational
        (\ q ->
          Both
            (Both (ENNLower x p) (ENNLower y q))
            (RationalLT r (addQ p q))))
ENNLower (productENN x y) r =
  Either
    (RationalLT r zeroQ)
    (Exists Rational
      (\ p ->
        Exists Rational
          (\ q ->
            Both
              (Both
                (RationalLT zeroQ p)
                (Both
                  (RationalLT zeroQ q)
                  (Both (ENNLower x p) (ENNLower y q))))
              (RationalLT r (multiplyQ p q)))))

ENNEqual : ENNReal -> ENNReal -> Set
ENNEqual x y =
  (r : Rational) ->
  Iff (ENNLower x r) (ENNLower y r)

ENNLE : ENNReal -> ENNReal -> Set
ENNLE x y =
  (r : Rational) ->
  ENNLower x r ->
  ENNLower y r

ENNStrictLess : ENNReal -> ENNReal -> Set
ENNStrictLess x y =
  Both (ENNLE x y) (Not (ENNEqual x y))

IsZeroENN : ENNReal -> Set
IsZeroENN x =
  (q : Rational) ->
  Iff (ENNLower x q) (RationalLT q zeroQ)

-- The canonical operation graphs are equality to total semantic constructors.
ENNAdd : ENNReal -> ENNReal -> ENNReal -> Set
ENNAdd x y z =
  ENNEqual z (sumENN x y)

ENNMultiply : ENNReal -> ENNReal -> ENNReal -> Set
ENNMultiply x y z =
  ENNEqual z (productENN x y)

IsSupremum :
  {p : Level} ->
  (ENNReal -> Set p) ->
  ENNReal ->
  Set (lsuc lzero ⊔ p)
IsSupremum candidates bound =
  Both
    ((x : ENNReal) -> candidates x -> ENNLE x bound)
    ((upper : ENNReal) ->
      ((x : ENNReal) -> candidates x -> ENNLE x upper) ->
      ENNLE bound upper)

IsInfimum :
  {p : Level} ->
  (ENNReal -> Set p) ->
  ENNReal ->
  Set (lsuc lzero ⊔ p)
IsInfimum candidates bound =
  Both
    ((x : ENNReal) -> candidates x -> ENNLE bound x)
    ((lowerBound : ENNReal) ->
      ((x : ENNReal) -> candidates x -> ENNLE lowerBound x) ->
      ENNLE lowerBound bound)

data FiniteSum
  (terms : Nat -> ENNReal) :
  Nat ->
  ENNReal ->
  Set1 where

  empty-sum :
    {value : ENNReal} ->
    IsZeroENN value ->
    FiniteSum terms zero value

  next-sum :
    {n : Nat} ->
    {partial total : ENNReal} ->
    FiniteSum terms n partial ->
    ENNAdd partial (terms n) total ->
    FiniteSum terms (suc n) total

CountableSum :
  (Nat -> ENNReal) ->
  ENNReal ->
  Set1
CountableSum terms total =
  IsSupremum
    (\ value ->
      Exists Nat (\ n -> FiniteSum terms n value))
    total

Predicate :
  {a : Level} ->
  Set a ->
  Set (a ⊔ lsuc lzero)
Predicate A =
  A -> Set

Empty :
  {a : Level} ->
  {A : Set a} ->
  Predicate A
Empty _ =
  Bottom

Complement :
  {a : Level} ->
  {A : Set a} ->
  Predicate A ->
  Predicate A
Complement S x =
  Not (S x)

Intersection :
  {a : Level} ->
  {A : Set a} ->
  Predicate A ->
  Predicate A ->
  Predicate A
Intersection S T x =
  Both (S x) (T x)

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
Subset {A = A} S T =
  (x : A) -> S x -> T x

SamePredicate :
  {a : Level} ->
  {A : Set a} ->
  Predicate A ->
  Predicate A ->
  Set a
SamePredicate {A = A} S T =
  (x : A) -> Iff (S x) (T x)

PairwiseDisjoint :
  {a : Level} ->
  {A : Set a} ->
  (Nat -> Predicate A) ->
  Set a
PairwiseDisjoint {a = a} {A = A} sets =
  (i j : Nat) ->
  i != j ->
  (x : A) ->
  sets i x ->
  sets j x ->
  Bottom {a}

record SigmaAlgebra
  {a : Level}
  (A : Set a) :
  Set (a ⊔ lsuc lzero) where
  field
    measurable :
      Predicate A ->
      Set

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

-- A measure is presented concretely by its outer mass together with the
-- outer-measure and Caratheodory laws. Countable additivity is stated with the
-- canonical extended-real countable sum above.
record Measure
  {a : Level}
  {A : Set a}
  (events : SigmaAlgebra A) :
  Set (a ⊔ lsuc lzero) where

  field
    mass :
      Predicate A ->
      ENNReal

    mass-congruent :
      (S T : Predicate A) ->
      SamePredicate S T ->
      ENNEqual (mass S) (mass T)

    mass-trimmed :
      (S : Predicate A) ->
      IsInfimum
        (\ value ->
          Exists (Predicate A)
            (\ T ->
              Both
                (measurable events T)
                (Both
                  (Subset S T)
                  (ENNEqual value (mass T)))))
        (mass S)

    mass-empty :
      IsZeroENN (mass Empty)

    mass-monotone :
      (S T : Predicate A) ->
      Subset S T ->
      ENNLE (mass S) (mass T)

    mass-countable-subadditive :
      (sets : Nat -> Predicate A) ->
      (sum : ENNReal) ->
      CountableSum (\ n -> mass (sets n)) sum ->
      ENNLE (mass (CountableUnion sets)) sum

    measurable-caratheodory :
      (S T : Predicate A) ->
      measurable events S ->
      ENNAdd
        (mass (Intersection T S))
        (mass (Intersection T (Complement S)))
        (mass T)

    measurable-countable-additivity :
      (sets : Nat -> Predicate A) ->
      ((n : Nat) -> measurable events (sets n)) ->
      PairwiseDisjoint sets ->
      CountableSum
        (\ n -> mass (sets n))
        (mass (CountableUnion sets))

open Measure

MeasureEqual :
  {a : Level} ->
  {A : Set a} ->
  {events : SigmaAlgebra A} ->
  Measure events ->
  Measure events ->
  Set (a ⊔ lsuc lzero)
MeasureEqual {A = A} {events = events} mu nu =
  (S : Predicate A) ->
  measurable events S ->
  ENNEqual (mass mu S) (mass nu S)

AbsolutelyContinuous :
  {a : Level} ->
  {A : Set a} ->
  {events : SigmaAlgebra A} ->
  Measure events ->
  Measure events ->
  Set (a ⊔ lsuc lzero)
AbsolutelyContinuous {A = A} mu nu =
  (S : Predicate A) ->
  IsZeroENN (mass nu S) ->
  IsZeroENN (mass mu S)

MutuallySingular :
  {a : Level} ->
  {A : Set a} ->
  {events : SigmaAlgebra A} ->
  Measure events ->
  Measure events ->
  Set (a ⊔ lsuc lzero)
MutuallySingular {A = A} {events = events} mu nu =
  Exists (Predicate A)
    (\ S ->
      Both
        (measurable events S)
        (Both
          (IsZeroENN (mass mu (Complement S)))
          (IsZeroENN (mass nu S))))

MeasurableENN :
  {a : Level} ->
  {A : Set a} ->
  SigmaAlgebra A ->
  (A -> ENNReal) ->
  Set1
MeasurableENN events f =
  (c : ENNReal) ->
  Both
    (measurable events (\ x -> ENNLE (f x) c))
    (measurable events (\ x -> ENNStrictLess c (f x)))

record IndexedSimpleBelowOn
  {a : Level}
  {A : Set a}
  (events : SigmaAlgebra A)
  (S : Predicate A)
  (f : A -> ENNReal) :
  Set (a ⊔ lsuc lzero) where

  field
    cutoff :
      Nat

    index :
      A ->
      Nat

    index-bounded :
      (x : A) ->
      index x <=N cutoff

    simpleValues :
      Nat ->
      ENNReal

    measurable-fibers :
      (n : Nat) ->
      measurable events (\ x -> index x == n)

    below-on-set :
      (x : A) ->
      Both
        (S x -> ENNLE (simpleValues (index x)) (f x))
        (Not (S x) -> IsZeroENN (simpleValues (index x)))

open IndexedSimpleBelowOn

SimpleIntegralValue :
  {a : Level} ->
  {A : Set a} ->
  {events : SigmaAlgebra A} ->
  (nu : Measure events) ->
  {S : Predicate A} ->
  {f : A -> ENNReal} ->
  IndexedSimpleBelowOn events S f ->
  ENNReal ->
  Set1
SimpleIntegralValue nu simple value =
  Exists (Nat -> ENNReal)
    (\ products ->
      Both
        ((n : Nat) ->
          ENNMultiply
            (simpleValues simple n)
            (mass nu (\ x -> index simple x == n))
            (products n))
        (FiniteSum products (suc (cutoff simple)) value))

SimpleIntegralCandidate :
  {a : Level} ->
  {A : Set a} ->
  {events : SigmaAlgebra A} ->
  Measure events ->
  Predicate A ->
  (A -> ENNReal) ->
  ENNReal ->
  Set (a ⊔ lsuc lzero)
SimpleIntegralCandidate nu S f value =
  Exists (IndexedSimpleBelowOn _ S f)
    (\ simple -> SimpleIntegralValue nu simple value)

LowerIntegralOnValue :
  {a : Level} ->
  {A : Set a} ->
  {events : SigmaAlgebra A} ->
  Measure events ->
  Predicate A ->
  (A -> ENNReal) ->
  ENNReal ->
  Set (a ⊔ lsuc lzero)
LowerIntegralOnValue nu S f value =
  IsSupremum
    (SimpleIntegralCandidate nu S f)
    value

-- A measure has the canonical withDensity values when every measurable-set
-- value is the lower integral of the density over that set.
DefinesWithDensity :
  {a : Level} ->
  {A : Set a} ->
  {events : SigmaAlgebra A} ->
  Measure events ->
  (A -> ENNReal) ->
  Measure events ->
  Set (a ⊔ lsuc lzero)
DefinesWithDensity {A = A} {events = events} nu f rho =
  (S : Predicate A) ->
  measurable events S ->
  LowerIntegralOnValue nu S f (mass rho S)

-- Since measures are trimmed, measurable-set equality is canonical measure
-- equality. This relation therefore states exactly nu.withDensity f = rho.
WithDensity :
  {a : Level} ->
  {A : Set a} ->
  {events : SigmaAlgebra A} ->
  Measure events ->
  (A -> ENNReal) ->
  Measure events ->
  Set (a ⊔ lsuc lzero)
WithDensity {events = events} nu f rho =
  Exists (Measure events)
    (\ weighted ->
      Both
        (DefinesWithDensity nu f weighted)
        (MeasureEqual weighted rho))

MeasureAdd :
  {a : Level} ->
  {A : Set a} ->
  {events : SigmaAlgebra A} ->
  Measure events ->
  Measure events ->
  Measure events ->
  Set (a ⊔ lsuc lzero)
MeasureAdd {A = A} mu nu total =
  (S : Predicate A) ->
  ENNAdd (mass mu S) (mass nu S) (mass total S)

-- The source theorem's typeclass contains a Lebesgue decomposition. Its
-- internal density is the Radon-Nikodym derivative selected by that instance.
record HaveLebesgueDecomposition
  {a : Level}
  {A : Set a}
  {events : SigmaAlgebra A}
  (mu nu : Measure events) :
  Set (a ⊔ lsuc lzero) where

  field
    singularPart :
      Measure events

    derivative :
      A ->
      ENNReal

    derivative-measurable :
      MeasurableENN events derivative

    densityPart :
      Measure events

    density-part-definition :
      DefinesWithDensity nu derivative densityPart

    singular-part-mutually-singular :
      MutuallySingular singularPart nu

    decomposition-equation :
      MeasureAdd singularPart densityPart mu

open HaveLebesgueDecomposition

rnDeriv :
  {a : Level} ->
  {A : Set a} ->
  {events : SigmaAlgebra A} ->
  {mu nu : Measure events} ->
  HaveLebesgueDecomposition mu nu ->
  A ->
  ENNReal
rnDeriv decomposition =
  derivative decomposition

radon-nikodym-theorem :
  {a : Level} ->
  Set (lsuc a)
radon-nikodym-theorem {a} =
  (A : Set a) ->
  (events : SigmaAlgebra A) ->
  (mu nu : Measure events) ->
  (decomposition : HaveLebesgueDecomposition mu nu) ->
  Iff
    (AbsolutelyContinuous mu nu)
    (WithDensity nu (rnDeriv decomposition) mu)
