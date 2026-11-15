-- Statement-only formalization of thousand-theorems corpus artifact Q182505,
-- "Bayes' theorem": for a finite measure and two measurable events, the
-- conditional mass of the second given the first equals the inverse mass of
-- the first times the conditional mass of the first given the second times
-- the mass of the second. This file contains no proof.

{-# OPTIONS --safe --prop #-}

module Q182505_bayes_theorem where

open import Agda.Primitive using (Level; lzero; lsuc; _⊔_; Prop)
open import Agda.Builtin.Nat using (Nat; zero; suc)

data Bottom {p : Level} : Prop p where

record Top {p : Level} : Prop p where
  constructor top

Not :
  {p : Level} ->
  Prop p ->
  Prop p
Not {p} proposition =
  proposition -> Bottom {p}

record Both
  {p q : Level}
  (A : Prop p)
  (B : Prop q) :
  Prop (p ⊔ q) where

  constructor both
  field
    first  : A
    second : B

data Either
  {p q : Level}
  (A : Prop p)
  (B : Prop q) :
  Prop (p ⊔ q) where

  left  : A -> Either A B
  right : B -> Either A B

record Iff
  {p q : Level}
  (A : Prop p)
  (B : Prop q) :
  Prop (p ⊔ q) where

  constructor equivalence
  field
    forward  : A -> B
    backward : B -> A

data Exists
  {a p : Level}
  (A : Set a)
  (P : A -> Prop p) :
  Prop (a ⊔ p) where

  witness :
    (value : A) ->
    P value ->
    Exists A P

infix 4 _==N_ _!=N_ _<=N_ _<N_
infixl 6 _+N_
infixl 7 _*N_

data _==N_ : Nat -> Nat -> Prop where
  reflN : {n : Nat} -> n ==N n

_!=N_ : Nat -> Nat -> Prop
m !=N n =
  Not (m ==N n)

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

data _<=N_ : Nat -> Nat -> Prop where
  zero<=   : {n : Nat} -> zero <=N n
  suc<=suc : {m n : Nat} -> m <=N n -> suc m <=N suc n

_<N_ : Nat -> Nat -> Prop
m <N n =
  suc m <=N n

-- A rational is the integer positivePart - negativePart divided by
-- suc denominatorCode. The relations below quotient this presentation.
record Rational : Set where
  constructor rational
  field
    positivePart    : Nat
    negativePart    : Nat
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

oneQ : Rational
oneQ =
  rational (suc zero) zero zero

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

RationalEqual : Rational -> Rational -> Prop
RationalEqual q r =
  ((positivePart q *N denominatorValue r) +N
   (negativePart r *N denominatorValue q))
  ==N
  ((positivePart r *N denominatorValue q) +N
   (negativePart q *N denominatorValue r))

RationalLE : Rational -> Rational -> Prop
RationalLE q r =
  ((positivePart q *N denominatorValue r) +N
   (negativePart r *N denominatorValue q))
  <=N
  ((positivePart r *N denominatorValue q) +N
   (negativePart q *N denominatorValue r))

RationalLT : Rational -> Rational -> Prop
RationalLT q r =
  ((positivePart q *N denominatorValue r) +N
   (negativePart r *N denominatorValue q))
  <N
  ((positivePart r *N denominatorValue q) +N
   (negativePart q *N denominatorValue r))

-- The fixed real object is the type of located lower Dedekind cuts of the
-- concrete rationals above. All cut laws are proof-irrelevant Prop fields.
record Real : Set1 where
  field
    lower :
      Rational ->
      Prop

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

open Real

record NonnegativeReal : Set1 where
  constructor nonnegative-real
  field
    real :
      Real

    nonnegative :
      (q : Rational) ->
      RationalLT q zeroQ ->
      lower real q

open NonnegativeReal

-- ENNReal is a fixed concrete syntax interpreted extensionally as a
-- nonnegative lower cut. The operation constructors denote the canonical
-- extended-real sum, product, and inverse through ENNLower below.
data ENNReal : Set1 where
  finite     : NonnegativeReal -> ENNReal
  infinity   : ENNReal
  sumENN     : ENNReal -> ENNReal -> ENNReal
  productENN : ENNReal -> ENNReal -> ENNReal
  inverseENN : ENNReal -> ENNReal

ENNLower : ENNReal -> Rational -> Prop
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
ENNLower (inverseENN x) r =
  Either
    (RationalLT r zeroQ)
    (Exists Rational
      (\ q ->
        Both
          (RationalLT r q)
          (Both
            (RationalLT zeroQ q)
            (Exists Rational
              (\ reciprocal ->
                Both
                  (RationalEqual (multiplyQ q reciprocal) oneQ)
                  (Exists Rational
                    (\ upperWitness ->
                      Both
                        (Not (ENNLower x upperWitness))
                        (RationalLT upperWitness reciprocal))))))))

ENNEqual : ENNReal -> ENNReal -> Prop
ENNEqual x y =
  (r : Rational) ->
  Iff (ENNLower x r) (ENNLower y r)

ENNLE : ENNReal -> ENNReal -> Prop
ENNLE x y =
  (r : Rational) ->
  ENNLower x r ->
  ENNLower y r

IsZeroENN : ENNReal -> Prop
IsZeroENN x =
  (q : Rational) ->
  Iff (ENNLower x q) (RationalLT q zeroQ)

IsSupremum :
  {p : Level} ->
  (ENNReal -> Prop p) ->
  ENNReal ->
  Prop (lsuc lzero ⊔ p)
IsSupremum candidates bound =
  Both
    ((x : ENNReal) -> candidates x -> ENNLE x bound)
    ((upper : ENNReal) ->
      ((x : ENNReal) -> candidates x -> ENNLE x upper) ->
      ENNLE bound upper)

IsInfimum :
  {p : Level} ->
  (ENNReal -> Prop p) ->
  ENNReal ->
  Prop (lsuc lzero ⊔ p)
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
  Prop (lsuc lzero) where

  empty-sum :
    {value : ENNReal} ->
    IsZeroENN value ->
    FiniteSum terms zero value

  next-sum :
    {n : Nat} ->
    {partial total : ENNReal} ->
    FiniteSum terms n partial ->
    ENNEqual total (sumENN partial (terms n)) ->
    FiniteSum terms (suc n) total

CountableSum :
  (Nat -> ENNReal) ->
  ENNReal ->
  Prop (lsuc lzero)
CountableSum terms total =
  IsSupremum
    (\ value ->
      Exists Nat (\ n -> FiniteSum terms n value))
    total

Event :
  {a : Level} ->
  Set a ->
  Set (a ⊔ lsuc lzero)
Event A =
  A -> Prop

Empty :
  {a : Level} ->
  {A : Set a} ->
  Event A
Empty _ =
  Bottom

Whole :
  {a : Level} ->
  {A : Set a} ->
  Event A
Whole _ =
  Top

Complement :
  {a : Level} ->
  {A : Set a} ->
  Event A ->
  Event A
Complement S x =
  Not (S x)

Intersection :
  {a : Level} ->
  {A : Set a} ->
  Event A ->
  Event A ->
  Event A
Intersection S T x =
  Both (S x) (T x)

CountableUnion :
  {a : Level} ->
  {A : Set a} ->
  (Nat -> Event A) ->
  Event A
CountableUnion sets x =
  Exists Nat (\ n -> sets n x)

Subset :
  {a : Level} ->
  {A : Set a} ->
  Event A ->
  Event A ->
  Prop a
Subset {A = A} S T =
  (x : A) -> S x -> T x

SameEvent :
  {a : Level} ->
  {A : Set a} ->
  Event A ->
  Event A ->
  Prop a
SameEvent {A = A} S T =
  (x : A) -> Iff (S x) (T x)

PairwiseDisjoint :
  {a : Level} ->
  {A : Set a} ->
  (Nat -> Event A) ->
  Prop a
PairwiseDisjoint {a = a} {A = A} sets =
  (i j : Nat) ->
  i !=N j ->
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
      Event A ->
      Prop

    measurable-empty :
      measurable Empty

    measurable-complement :
      (S : Event A) ->
      measurable S ->
      measurable (Complement S)

    measurable-countable-union :
      (sets : Nat -> Event A) ->
      ((n : Nat) -> measurable (sets n)) ->
      measurable (CountableUnion sets)

    measurable-congruent :
      (S T : Event A) ->
      SameEvent S T ->
      measurable S ->
      measurable T

open SigmaAlgebra

-- A measure is represented by its outer mass, the outer-measure laws, and
-- Caratheodory measurability. Every law is Prop-valued and hence irrelevant.
record Measure
  {a : Level}
  {A : Set a}
  (events : SigmaAlgebra A) :
  Set (a ⊔ lsuc lzero) where

  field
    mass :
      Event A ->
      ENNReal

    mass-congruent :
      (S T : Event A) ->
      SameEvent S T ->
      ENNEqual (mass S) (mass T)

    mass-trimmed :
      (S : Event A) ->
      IsInfimum
        (\ value ->
          Exists (Event A)
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
      (S T : Event A) ->
      Subset S T ->
      ENNLE (mass S) (mass T)

    mass-countable-subadditive :
      (sets : Nat -> Event A) ->
      (sum : ENNReal) ->
      CountableSum (\ n -> mass (sets n)) sum ->
      ENNLE (mass (CountableUnion sets)) sum

    measurable-caratheodory :
      (S T : Event A) ->
      measurable events S ->
      ENNEqual
        (mass T)
        (sumENN
          (mass (Intersection T S))
          (mass (Intersection T (Complement S))))

    measurable-countable-additivity :
      (sets : Nat -> Event A) ->
      ((n : Nat) -> measurable events (sets n)) ->
      PairwiseDisjoint sets ->
      CountableSum
        (\ n -> mass (sets n))
        (mass (CountableUnion sets))

open Measure

FiniteMeasure :
  {a : Level} ->
  {A : Set a} ->
  {events : SigmaAlgebra A} ->
  Measure events ->
  Prop
FiniteMeasure measure =
  Not (ENNEqual (mass measure Whole) infinity)

-- Restriction is canonical: its value at event is the original mass of the
-- intersection. It is a definition, not an additional theorem hypothesis.
restrictedMass :
  {a : Level} ->
  {A : Set a} ->
  {events : SigmaAlgebra A} ->
  Measure events ->
  Event A ->
  Event A ->
  ENNReal
restrictedMass measure given event =
  mass measure (Intersection event given)

conditionalMass :
  {a : Level} ->
  {A : Set a} ->
  {events : SigmaAlgebra A} ->
  Measure events ->
  Event A ->
  Event A ->
  ENNReal
conditionalMass measure given event =
  productENN
    (inverseENN (mass measure given))
    (restrictedMass measure given event)

bayes-theorem :
  {a : Level} ->
  Prop (lsuc a)
bayes-theorem {a} =
  (A : Set a) ->
  (events : SigmaAlgebra A) ->
  (s t : Event A) ->
  measurable events s ->
  measurable events t ->
  (measure : Measure events) ->
  FiniteMeasure measure ->
  ENNEqual
    (conditionalMass measure s t)
    (productENN
      (productENN
        (inverseENN (mass measure s))
        (conditionalMass measure t s))
      (mass measure t))
