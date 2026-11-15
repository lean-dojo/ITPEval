-- Statement-only formalization of thousand-theorems corpus artifact Q3526996,
-- "Kolmogorov extension theorem": a projective family of finite Borel measures
-- on finite subproducts of Polish spaces extends to a measure on the full
-- dependent product with exactly those finite-dimensional marginals. This file contains no proof.

{-# OPTIONS --safe --prop #-}

module Q3526996_kolmogorov_extension_theorem where

open import Agda.Primitive using (Level; lzero; lsuc; _⊔_; Prop; Setω)
open import Agda.Builtin.Equality renaming (_≡_ to _==_)
open import Agda.Builtin.Nat using (Nat; zero; suc)

data Fin : Nat -> Set where
  fzero : {n : Nat} -> Fin (suc n)
  fsuc  : {n : Nat} -> Fin n -> Fin (suc n)

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

addQ : Rational -> Rational -> Rational
addQ q r =
  rational
    ((positivePart q *N denominatorValue r) +N
     (positivePart r *N denominatorValue q))
    ((negativePart q *N denominatorValue r) +N
     (negativePart r *N denominatorValue q))
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

record NonnegativeCut : Set1 where
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

    nonnegative :
      (q : Rational) ->
      RationalLT q zeroQ ->
      lower q

open NonnegativeCut

data ENNReal : Set1 where
  zeroENN : ENNReal
  finite  : NonnegativeCut -> ENNReal
  infinity : ENNReal
  sumENN  : ENNReal -> ENNReal -> ENNReal

ENNLower : ENNReal -> Rational -> Prop
ENNLower zeroENN q =
  RationalLT q zeroQ
ENNLower (finite x) q =
  lower x q
ENNLower infinity q =
  Top
ENNLower (sumENN x y) r =
  Exists Rational
    (\ p ->
      Exists Rational
        (\ q ->
          Both
            (Both (ENNLower x p) (ENNLower y q))
            (RationalLT r (addQ p q))))

ENNEqual : ENNReal -> ENNReal -> Prop
ENNEqual x y =
  (q : Rational) ->
  Iff (ENNLower x q) (ENNLower y q)

ENNLE : ENNReal -> ENNReal -> Prop
ENNLE x y =
  (q : Rational) ->
  ENNLower x q ->
  ENNLower y q

ENNStrictLess : ENNReal -> ENNReal -> Prop
ENNStrictLess x y =
  Both (ENNLE x y) (Not (ENNEqual x y))

IsZeroENN : ENNReal -> Prop
IsZeroENN x =
  ENNEqual x zeroENN

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

data FiniteSum
  (terms : Nat -> ENNReal) :
  Nat ->
  ENNReal ->
  Prop (lsuc lzero) where

  empty-sum :
    FiniteSum terms zero zeroENN

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
  (x : A) ->
  S x ->
  T x

SameEvent :
  {a : Level} ->
  {A : Set a} ->
  Event A ->
  Event A ->
  Prop a
SameEvent {A = A} S T =
  (x : A) ->
  Iff (S x) (T x)

PairwiseDisjoint :
  {a : Level} ->
  {A : Set a} ->
  (Nat -> Event A) ->
  Prop a
PairwiseDisjoint {a = a} {A = A} sets =
  (m n : Nat) ->
  m !=N n ->
  (x : A) ->
  sets m x ->
  sets n x ->
  Bottom {a}

Preimage :
  {a b : Level} ->
  {A : Set a} ->
  {B : Set b} ->
  (A -> B) ->
  Event B ->
  Event A
Preimage f E x =
  E (f x)

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

record Measure
  {a p : Level}
  {A : Set a}
  (events : Event A -> Prop p) :
  Set (a ⊔ p ⊔ lsuc lzero) where

  field
    mass :
      Event A ->
      ENNReal

    mass-congruent :
      (S T : Event A) ->
      SameEvent S T ->
      ENNEqual (mass S) (mass T)

    mass-empty :
      IsZeroENN (mass Empty)

    mass-countable-additivity :
      (sets : Nat -> Event A) ->
      ((n : Nat) -> events (sets n)) ->
      PairwiseDisjoint sets ->
      CountableSum
        (\ n -> mass (sets n))
        (mass (CountableUnion sets))

open Measure

FiniteMeasure :
  {a p : Level} ->
  {A : Set a} ->
  {events : Event A -> Prop p} ->
  Measure events ->
  Prop
FiniteMeasure measure =
  Not (ENNEqual (mass measure Whole) infinity)

record MetricSpace
  {a : Level}
  (A : Set a) :
  Set (a ⊔ lsuc lzero) where

  field
    distance :
      A ->
      A ->
      ENNReal

    distance-finite :
      (x y : A) ->
      Not (ENNEqual (distance x y) infinity)

    distance-self :
      (x : A) ->
      IsZeroENN (distance x x)

    distance-symmetric :
      (x y : A) ->
      ENNEqual (distance x y) (distance y x)

    distance-triangle :
      (x y z : A) ->
      ENNLE
        (distance x z)
        (sumENN (distance x y) (distance y z))

    distance-separates :
      (x y : A) ->
      IsZeroENN (distance x y) ->
      x == y

open MetricSpace

PositiveFinite : ENNReal -> Prop
PositiveFinite radius =
  Both
    (ENNStrictLess zeroENN radius)
    (Not (ENNEqual radius infinity))

OpenBall :
  {a : Level} ->
  {A : Set a} ->
  MetricSpace A ->
  A ->
  ENNReal ->
  Event A
OpenBall metric center radius x =
  ENNStrictLess (distance metric x center) radius

MetricOpen :
  {a : Level} ->
  {A : Set a} ->
  MetricSpace A ->
  Event A ->
  Prop (a ⊔ lsuc lzero)
MetricOpen {A = A} metric U =
  (x : A) ->
  U x ->
  Exists ENNReal
    (\ radius ->
      Both
        (PositiveFinite radius)
        (Subset (OpenBall metric x radius) U))

SequentialLimit :
  {a : Level} ->
  {A : Set a} ->
  MetricSpace A ->
  (Nat -> A) ->
  A ->
  Prop (lsuc lzero)
SequentialLimit metric sequence limit =
  (epsilon : ENNReal) ->
  PositiveFinite epsilon ->
  Exists Nat
    (\ cutoff ->
      (n : Nat) ->
      cutoff <=N n ->
      ENNStrictLess
        (distance metric (sequence n) limit)
        epsilon)

CauchySequence :
  {a : Level} ->
  {A : Set a} ->
  MetricSpace A ->
  (Nat -> A) ->
  Prop (lsuc lzero)
CauchySequence metric sequence =
  (epsilon : ENNReal) ->
  PositiveFinite epsilon ->
  Exists Nat
    (\ cutoff ->
      (m n : Nat) ->
      cutoff <=N m ->
      cutoff <=N n ->
      ENNStrictLess
        (distance metric (sequence m) (sequence n))
        epsilon)

CompleteMetric :
  {a : Level} ->
  {A : Set a} ->
  MetricSpace A ->
  Prop (a ⊔ lsuc lzero)
CompleteMetric {A = A} metric =
  (sequence : Nat -> A) ->
  CauchySequence metric sequence ->
  Exists A
    (\ limit ->
      SequentialLimit metric sequence limit)

record SecondCountableMetric
  {a : Level}
  {A : Set a}
  (metric : MetricSpace A) :
  Set (a ⊔ lsuc lzero) where

  field
    countable-basis :
      Nat ->
      Event A

    basis-open :
      (n : Nat) ->
      MetricOpen metric (countable-basis n)

    basis-refines :
      (U : Event A) ->
      MetricOpen metric U ->
      (x : A) ->
      U x ->
      Exists Nat
        (\ n ->
          Both
            (countable-basis n x)
            (Subset (countable-basis n) U))

record PolishSpace
  {a : Level}
  {A : Set a}
  (metric : MetricSpace A) :
  Set (a ⊔ lsuc lzero) where

  field
    complete :
      CompleteMetric metric

    second-countable :
      SecondCountableMetric metric

data BorelGenerated
  {a : Level}
  {A : Set a}
  (metric : MetricSpace A) :
  Event A ->
  Prop (a ⊔ lsuc lzero) where

  borel-open :
    {U : Event A} ->
    MetricOpen metric U ->
    BorelGenerated metric U

  borel-empty :
    BorelGenerated metric Empty

  borel-complement :
    {S : Event A} ->
    BorelGenerated metric S ->
    BorelGenerated metric (Complement S)

  borel-countable-union :
    (sets : Nat -> Event A) ->
    ((n : Nat) -> BorelGenerated metric (sets n)) ->
    BorelGenerated metric (CountableUnion sets)

  borel-congruent :
    {S T : Event A} ->
    SameEvent S T ->
    BorelGenerated metric S ->
    BorelGenerated metric T

record BorelSpace
  {a : Level}
  {A : Set a}
  (metric : MetricSpace A)
  (events : SigmaAlgebra A) :
  Set (a ⊔ lsuc lzero) where

  field
    borel-measurable :
      (S : Event A) ->
      BorelGenerated metric S ->
      measurable events S

    measurable-borel :
      (S : Event A) ->
      measurable events S ->
      BorelGenerated metric S

record FiniteWitness
  {a : Level}
  (A : Set a) :
  Set a where

  field
    size :
      Nat

    enumerate :
      Fin size ->
      A

    locate :
      A ->
      Fin size

    enumerate-locate :
      (x : A) ->
      enumerate (locate x) == x

    locate-enumerate :
      (k : Fin size) ->
      locate (enumerate k) == k

record FiniteCoordinates
  {i : Level}
  (I : Set i) :
  Set (lsuc i) where

  field
    Carrier :
      Set i

    carrier-finite :
      FiniteWitness Carrier

    coordinate :
      Carrier ->
      I

    coordinate-injective :
      (j k : Carrier) ->
      coordinate j == coordinate k ->
      j == k

open FiniteCoordinates

record CoordinateInclusion
  {i : Level}
  {I : Set i}
  (J K : FiniteCoordinates I) :
  Set i where

  field
    include :
      Carrier J ->
      Carrier K

    coordinate-preserving :
      (j : Carrier J) ->
      coordinate K (include j) == coordinate J j

open CoordinateInclusion

transport :
  {i a : Level} ->
  {I : Set i} ->
  {A : I -> Set a} ->
  {x y : I} ->
  x == y ->
  A x ->
  A y
transport {A = A} refl value =
  value

FiniteSection :
  {i a : Level} ->
  {I : Set i} ->
  (A : I -> Set a) ->
  FiniteCoordinates I ->
  Set (i ⊔ a)
FiniteSection A J =
  (j : Carrier J) ->
  A (coordinate J j)

FullSection :
  {i a : Level} ->
  {I : Set i} ->
  (I -> Set a) ->
  Set (i ⊔ a)
FullSection {I = I} A =
  (i : I) ->
  A i

restrictSection :
  {i a : Level} ->
  {I : Set i} ->
  {A : I -> Set a} ->
  {J K : FiniteCoordinates I} ->
  CoordinateInclusion J K ->
  FiniteSection A K ->
  FiniteSection A J
restrictSection {A = A} inclusion section j =
  transport {A = A}
    (coordinate-preserving inclusion j)
    (section (include inclusion j))

projectSection :
  {i a : Level} ->
  {I : Set i} ->
  {A : I -> Set a} ->
  (J : FiniteCoordinates I) ->
  FullSection A ->
  FiniteSection A J
projectSection J section j =
  section (coordinate J j)

data FiniteProductMeasurable
  {i a : Level}
  {I : Set i}
  (A : I -> Set a)
  (spaces : (i : I) -> SigmaAlgebra (A i))
  (J : FiniteCoordinates I) :
  Event (FiniteSection A J) ->
  Prop (i ⊔ a ⊔ lsuc lzero) where

  finite-coordinate-event :
    (j : Carrier J) ->
    (E : Event (A (coordinate J j))) ->
    measurable (spaces (coordinate J j)) E ->
    FiniteProductMeasurable A spaces J
      (\ section -> E (section j))

  finite-empty :
    FiniteProductMeasurable A spaces J Empty

  finite-complement :
    {S : Event (FiniteSection A J)} ->
    FiniteProductMeasurable A spaces J S ->
    FiniteProductMeasurable A spaces J (Complement S)

  finite-countable-union :
    (sets : Nat -> Event (FiniteSection A J)) ->
    ((n : Nat) ->
      FiniteProductMeasurable A spaces J (sets n)) ->
    FiniteProductMeasurable A spaces J (CountableUnion sets)

  finite-congruent :
    {S T : Event (FiniteSection A J)} ->
    SameEvent S T ->
    FiniteProductMeasurable A spaces J S ->
    FiniteProductMeasurable A spaces J T

data FullProductMeasurable
  {i a : Level}
  {I : Set i}
  (A : I -> Set a)
  (spaces : (i : I) -> SigmaAlgebra (A i)) :
  Event (FullSection A) ->
  Prop (i ⊔ a ⊔ lsuc lzero) where

  full-coordinate-event :
    (i : I) ->
    (E : Event (A i)) ->
    measurable (spaces i) E ->
    FullProductMeasurable A spaces
      (\ section -> E (section i))

  full-empty :
    FullProductMeasurable A spaces Empty

  full-complement :
    {S : Event (FullSection A)} ->
    FullProductMeasurable A spaces S ->
    FullProductMeasurable A spaces (Complement S)

  full-countable-union :
    (sets : Nat -> Event (FullSection A)) ->
    ((n : Nat) ->
      FullProductMeasurable A spaces (sets n)) ->
    FullProductMeasurable A spaces (CountableUnion sets)

  full-congruent :
    {S T : Event (FullSection A)} ->
    SameEvent S T ->
    FullProductMeasurable A spaces S ->
    FullProductMeasurable A spaces T

IsProjectiveMeasureFamily :
  {i a : Level} ->
  {I : Set i} ->
  {A : I -> Set a} ->
  {spaces : (i : I) -> SigmaAlgebra (A i)} ->
  ((J : FiniteCoordinates I) ->
    Measure (FiniteProductMeasurable A spaces J)) ->
  Prop (lsuc i ⊔ a)
IsProjectiveMeasureFamily {A = A} {spaces = spaces} family =
  (J K : FiniteCoordinates _) ->
  (inclusion : CoordinateInclusion J K) ->
  (E : Event (FiniteSection A J)) ->
  FiniteProductMeasurable A spaces J E ->
  ENNEqual
    (mass (family K)
      (Preimage (restrictSection {A = A} inclusion) E))
    (mass (family J) E)

IsProjectiveLimit :
  {i a : Level} ->
  {I : Set i} ->
  {A : I -> Set a} ->
  {spaces : (i : I) -> SigmaAlgebra (A i)} ->
  Measure (FullProductMeasurable A spaces) ->
  ((J : FiniteCoordinates I) ->
    Measure (FiniteProductMeasurable A spaces J)) ->
  Prop (lsuc i ⊔ a)
IsProjectiveLimit {A = A} {spaces = spaces} limit family =
  (J : FiniteCoordinates _) ->
  (E : Event (FiniteSection A J)) ->
  FiniteProductMeasurable A spaces J E ->
  ENNEqual
    (mass limit (Preimage (projectSection J) E))
    (mass (family J) E)

record ProjectiveLimitWitness
  {i a : Level}
  {I : Set i}
  {A : I -> Set a}
  {spaces : (i : I) -> SigmaAlgebra (A i)}
  (family :
    (J : FiniteCoordinates I) ->
    Measure (FiniteProductMeasurable A spaces J)) :
  Set (lsuc i ⊔ a ⊔ lsuc lzero) where

  field
    projective-limit :
      Measure (FullProductMeasurable A spaces)

    has-prescribed-marginals :
      IsProjectiveLimit projective-limit family

kolmogorov-extension-theorem : Setω
kolmogorov-extension-theorem =
  {i a : Level} ->
  (I : Set i) ->
  (A : I -> Set a) ->
  (spaces : (index : I) -> SigmaAlgebra (A index)) ->
  (metrics : (index : I) -> MetricSpace (A index)) ->
  ((index : I) -> BorelSpace (metrics index) (spaces index)) ->
  ((index : I) -> PolishSpace (metrics index)) ->
  (family :
    (J : FiniteCoordinates I) ->
    Measure (FiniteProductMeasurable A spaces J)) ->
  ((J : FiniteCoordinates I) -> FiniteMeasure (family J)) ->
  IsProjectiveMeasureFamily family ->
  ProjectiveLimitWitness family
