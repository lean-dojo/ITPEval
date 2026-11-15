-- Statement-only formalization of thousand-theorems corpus artifact Q25378690,
-- "Ionescu-Tulcea theorem": a sequence of measurable Markov kernels on finite
-- histories extends to a measurable Markov kernel on infinite trajectories
-- with the prescribed iterated finite-dimensional laws. This file contains no proof.

{-# OPTIONS --safe --prop #-}

module Q25378690_ionescu_tulcea_theorem where

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
m +N zero =
  m
m +N suc n =
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

data ENNReal : Set1 where
  finite     : NonnegativeReal -> ENNReal
  infinity   : ENNReal
  sumENN     : ENNReal -> ENNReal -> ENNReal
  productENN : ENNReal -> ENNReal -> ENNReal

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

IsOneENN : ENNReal -> Prop
IsOneENN x =
  (q : Rational) ->
  Iff (ENNLower x q) (RationalLT q oneQ)

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

MeasurableMap :
  {a b : Level} ->
  {A : Set a} ->
  {B : Set b} ->
  SigmaAlgebra A ->
  SigmaAlgebra B ->
  (A -> B) ->
  Prop (b ⊔ lsuc lzero)
MeasurableMap source target f =
  (E : Event _) ->
  measurable target E ->
  measurable source (\ x -> E (f x))

ENNMeasurable :
  {a : Level} ->
  {A : Set a} ->
  SigmaAlgebra A ->
  (A -> ENNReal) ->
  Prop
ENNMeasurable events f =
  (q : Rational) ->
  measurable events (\ x -> ENNLower (f x) q)

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

ProbabilityMeasure :
  {a : Level} ->
  {A : Set a} ->
  {events : SigmaAlgebra A} ->
  Measure events ->
  Prop
ProbabilityMeasure measure =
  IsOneENN (mass measure Whole)

MeasureEqual :
  {a : Level} ->
  {A : Set a} ->
  {events : SigmaAlgebra A} ->
  Measure events ->
  Measure events ->
  Prop (a ⊔ lsuc lzero)
MeasureEqual {events = events} mu nu =
  (E : Event _) ->
  measurable events E ->
  ENNEqual (mass mu E) (mass nu E)

record SimpleFunctionBelow
  {a : Level}
  {A : Set a}
  (events : SigmaAlgebra A)
  (f : A -> ENNReal) :
  Set (a ⊔ lsuc lzero) where

  field
    cutoff :
      Nat

    simpleIndex :
      A ->
      Nat

    simpleValues :
      Nat ->
      ENNReal

    simpleIndexWithin :
      (x : A) ->
      simpleIndex x <=N cutoff

    simpleFiberMeasurable :
      (i : Nat) ->
      i <=N cutoff ->
      measurable events (\ x -> simpleIndex x ==N i)

    simplePointwiseBelow :
      (x : A) ->
      ENNLE (simpleValues (simpleIndex x)) (f x)

open SimpleFunctionBelow

SimpleIntegralValue :
  {a : Level} ->
  {A : Set a} ->
  {events : SigmaAlgebra A} ->
  (measure : Measure events) ->
  {f : A -> ENNReal} ->
  SimpleFunctionBelow events f ->
  ENNReal ->
  Prop (lsuc lzero)
SimpleIntegralValue measure simple value =
  FiniteSum
    (\ i ->
      productENN
        (simpleValues simple i)
        (mass measure (\ x -> simpleIndex simple x ==N i)))
    (suc (cutoff simple))
    value

LIntegral :
  {a : Level} ->
  {A : Set a} ->
  {events : SigmaAlgebra A} ->
  Measure events ->
  (A -> ENNReal) ->
  ENNReal ->
  Prop (a ⊔ lsuc lzero)
LIntegral measure f value =
  IsSupremum
    (\ candidate ->
      Exists (SimpleFunctionBelow _ f)
        (\ simple -> SimpleIntegralValue measure simple candidate))
    value

data Prefix
  {a : Level}
  (X : Nat -> Set a) :
  Nat ->
  Set a where

  start :
    X zero ->
    Prefix X zero

  snoc :
    {n : Nat} ->
    Prefix X n ->
    X (suc n) ->
    Prefix X (suc n)

data Index : Nat -> Nat -> Set where
  first :
    Index zero zero

  last :
    {n : Nat} ->
    Index (suc n) (suc n)

  weaken :
    {i n : Nat} ->
    Index i n ->
    Index i (suc n)

lookup :
  {a : Level} ->
  {X : Nat -> Set a} ->
  {i n : Nat} ->
  Index i n ->
  Prefix X n ->
  X i
lookup first (start x) =
  x
lookup last (snoc history x) =
  x
lookup (weaken i) (snoc history x) =
  lookup i history

Trajectory :
  {a : Level} ->
  (Nat -> Set a) ->
  Set a
Trajectory X =
  (n : Nat) -> X n

restrictTrajectory :
  {a : Level} ->
  {X : Nat -> Set a} ->
  (n : Nat) ->
  Trajectory X ->
  Prefix X n
restrictTrajectory zero path =
  start (path zero)
restrictTrajectory (suc n) path =
  snoc (restrictTrajectory n path) (path (suc n))

record ProductMeasurableSpaces
  {a : Level}
  (X : Nat -> Set a)
  (base : (n : Nat) -> SigmaAlgebra (X n)) :
  Set (a ⊔ lsuc lzero) where

  field
    prefix :
      (n : Nat) ->
      SigmaAlgebra (Prefix X n)

    full :
      SigmaAlgebra (Trajectory X)

    prefix-coordinate-measurable :
      (i n : Nat) ->
      (index : Index i n) ->
      MeasurableMap (prefix n) (base i) (lookup index)

    prefix-generated :
      (n : Nat) ->
      (candidate : SigmaAlgebra (Prefix X n)) ->
      ((i : Nat) ->
        (index : Index i n) ->
        MeasurableMap candidate (base i) (lookup index)) ->
      (E : Event (Prefix X n)) ->
      measurable (prefix n) E ->
      measurable candidate E

    full-coordinate-measurable :
      (i : Nat) ->
      MeasurableMap full (base i) (\ path -> path i)

    full-generated :
      (candidate : SigmaAlgebra (Trajectory X)) ->
      ((i : Nat) ->
        MeasurableMap candidate (base i) (\ path -> path i)) ->
      (E : Event (Trajectory X)) ->
      measurable full E ->
      measurable candidate E

open ProductMeasurableSpaces

record Kernel
  {a : Level}
  {A B : Set a}
  (source : SigmaAlgebra A)
  (target : SigmaAlgebra B) :
  Set (a ⊔ lsuc lzero) where

  field
    applyKernel :
      A ->
      Measure target

    measurable-evaluation :
      (E : Event B) ->
      measurable target E ->
      ENNMeasurable source (\ x -> mass (applyKernel x) E)

open Kernel

MarkovKernel :
  {a : Level} ->
  {A B : Set a} ->
  {source : SigmaAlgebra A} ->
  {target : SigmaAlgebra B} ->
  Kernel source target ->
  Prop a
MarkovKernel {A = A} kernel =
  (x : A) ->
  ProbabilityMeasure (applyKernel kernel x)

DiracAt :
  {a : Level} ->
  {A : Set a} ->
  {events : SigmaAlgebra A} ->
  Measure events ->
  A ->
  Prop (a ⊔ lsuc lzero)
DiracAt {events = events} measure point =
  (E : Event _) ->
  measurable events E ->
  Both
    (E point -> IsOneENN (mass measure E))
    (Not (E point) -> IsZeroENN (mass measure E))

KernelStep :
  {a : Level} ->
  {X : Nat -> Set a} ->
  {base : (n : Nat) -> SigmaAlgebra (X n)} ->
  (spaces : ProductMeasurableSpaces X base) ->
  (n : Nat) ->
  Measure (prefix spaces n) ->
  Kernel (prefix spaces n) (base (suc n)) ->
  Measure (prefix spaces (suc n)) ->
  Prop (a ⊔ lsuc lzero)
KernelStep spaces n previous transition next =
  (E : Event (Prefix _ (suc n))) ->
  measurable (prefix spaces (suc n)) E ->
  Exists ENNReal
    (\ integral ->
      Both
        (LIntegral previous
          (\ history ->
            mass
              (applyKernel transition history)
              (\ nextValue -> E (snoc history nextValue)))
          integral)
        (ENNEqual (mass next E) integral))

FiniteLawFamily :
  {a : Level} ->
  {X : Nat -> Set a} ->
  {base : (n : Nat) -> SigmaAlgebra (X n)} ->
  ProductMeasurableSpaces X base ->
  Nat ->
  Set (a ⊔ lsuc lzero)
FiniteLawFamily {X = X} spaces a =
  (k : Nat) ->
  Prefix X a ->
  Measure (prefix spaces (a +N k))

record IsIonescuTulceaExtension
  {a : Level}
  {X : Nat -> Set a}
  {base : (n : Nat) -> SigmaAlgebra (X n)}
  (spaces : ProductMeasurableSpaces X base)
  (transitions :
    (n : Nat) ->
    Kernel (prefix spaces n) (base (suc n)))
  (cutoff : Nat)
  (trajectoryKernel :
    Kernel (prefix spaces cutoff) (full spaces))
  (finiteLaw : FiniteLawFamily spaces cutoff) :
  Prop (a ⊔ lsuc lzero) where

  field
    trajectory-is-markov :
      MarkovKernel trajectoryKernel

    finite-laws-are-probability :
      (k : Nat) ->
      (history : Prefix X cutoff) ->
      ProbabilityMeasure (finiteLaw k history)

    initial-law :
      (history : Prefix X cutoff) ->
      DiracAt (finiteLaw zero history) history

    successor-law :
      (k : Nat) ->
      (history : Prefix X cutoff) ->
      KernelStep
        spaces
        (cutoff +N k)
        (finiteLaw k history)
        (transitions (cutoff +N k))
        (finiteLaw (suc k) history)

    finite-marginals :
      (k : Nat) ->
      (history : Prefix X cutoff) ->
      (E : Event (Prefix X (cutoff +N k))) ->
      measurable (prefix spaces (cutoff +N k)) E ->
      ENNEqual
        (mass
          (applyKernel trajectoryKernel history)
          (\ path -> E (restrictTrajectory (cutoff +N k) path)))
        (mass (finiteLaw k history) E)

ionescu-tulcea-theorem :
  {a : Level} ->
  Prop (lsuc a)
ionescu-tulcea-theorem {a} =
  (X : Nat -> Set a) ->
  (base : (n : Nat) -> SigmaAlgebra (X n)) ->
  (spaces : ProductMeasurableSpaces X base) ->
  (transitions :
    (n : Nat) ->
    Kernel (prefix spaces n) (base (suc n))) ->
  ((n : Nat) -> MarkovKernel (transitions n)) ->
  (cutoff : Nat) ->
  Exists
    (Kernel (prefix spaces cutoff) (full spaces))
    (\ trajectoryKernel ->
      Exists
        (FiniteLawFamily spaces cutoff)
        (\ finiteLaw ->
          IsIonescuTulceaExtension
            spaces
            transitions
            cutoff
            trajectoryKernel
            finiteLaw))
