-- Statement-only formalization of thousand-theorems corpus artifact Q258374,
-- "Carathéodory's theorem (measure theory)": under classical logic, every
-- outer measure determines the measurable space of sets satisfying
-- Carathéodory's splitting criterion. This file contains no proof.

{-# OPTIONS --safe --prop #-}

module Q258374_carath_odory_s_theorem_measure_theory where

open import Agda.Primitive using (Level; lzero; lsuc; _⊔_; Prop)
open import Agda.Builtin.Nat using (Nat; zero; suc)

data Bottom {p : Level} : Prop p where

record Top {p : Level} : Prop p where
  constructor top

Not :
  {p : Level} ->
  Prop p ->
  Prop p
Not {p} A =
  A -> Bottom {p}

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

ExcludedMiddle :
  (p : Level) ->
  Prop (lsuc p)
ExcludedMiddle p =
  (P : Prop p) ->
  Either P (Not P)

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

infix 4 _==N_ _<=N_ _<N_
infixl 6 _+N_
infixl 7 _*N_

data _==N_ : Nat -> Nat -> Prop where
  reflN : {n : Nat} -> n ==N n

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

-- Rationals are represented by an integer numerator and a positive
-- denominator. Equality and order below quotient this presentation.
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

RationalLT : Rational -> Rational -> Prop
RationalLT q r =
  ((positivePart q *N denominatorValue r) +N
   (negativePart r *N denominatorValue q))
  <N
  ((positivePart r *N denominatorValue q) +N
   (negativePart q *N denominatorValue r))

-- Finite real values are located lower Dedekind cuts of the rationals.
record DedekindReal : Set1 where
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

-- The syntax is interpreted extensionally by lower cuts. The operation
-- constructors give exact extended-nonnegative-real addition and countable
-- summation; countable summation is therefore total, as it is in Lean.
data ENNReal : Set1 where
  zeroENN         : ENNReal
  finite          : NonnegativeReal -> ENNReal
  infinity        : ENNReal
  sumENN          : ENNReal -> ENNReal -> ENNReal
  countableSumENN : (Nat -> ENNReal) -> ENNReal

mutual
  ENNLower : ENNReal -> Rational -> Prop
  ENNLower zeroENN q =
    RationalLT q zeroQ
  ENNLower (finite x) q =
    lower (real x) q
  ENNLower infinity q =
    Top
  ENNLower (sumENN x y) q =
    Exists Rational
      (\ r ->
        Exists Rational
          (\ s ->
            Both
              (Both (ENNLower x r) (ENNLower y s))
              (RationalLT q (addQ r s))))
  ENNLower (countableSumENN terms) q =
    Exists Nat (\ n -> FinitePrefixLower terms n q)

  data FinitePrefixLower
    (terms : Nat -> ENNReal) :
    Nat ->
    Rational ->
    Prop where

    empty-prefix-lower :
      {q : Rational} ->
      RationalLT q zeroQ ->
      FinitePrefixLower terms zero q

    next-prefix-lower :
      {n : Nat} ->
      {p r q : Rational} ->
      FinitePrefixLower terms n p ->
      ENNLower (terms n) r ->
      RationalLT q (addQ p r) ->
      FinitePrefixLower terms (suc n) q

ENNEqual : ENNReal -> ENNReal -> Prop
ENNEqual x y =
  (q : Rational) ->
  Iff (ENNLower x q) (ENNLower y q)

ENNLE : ENNReal -> ENNReal -> Prop
ENNLE x y =
  (q : Rational) ->
  ENNLower x q ->
  ENNLower y q

IsZeroENN : ENNReal -> Prop
IsZeroENN x =
  (q : Rational) ->
  Iff (ENNLower x q) (RationalLT q zeroQ)

Predicate :
  {a : Level} ->
  Set a ->
  Set (a ⊔ lsuc lzero)
Predicate A =
  A -> Prop

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

Difference :
  {a : Level} ->
  {A : Set a} ->
  Predicate A ->
  Predicate A ->
  Predicate A
Difference S T =
  Intersection S (Complement T)

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
  Prop a
Subset {A = A} S T =
  (x : A) ->
  S x ->
  T x

SamePredicate :
  {a : Level} ->
  {A : Set a} ->
  Predicate A ->
  Predicate A ->
  Prop a
SamePredicate {A = A} S T =
  (x : A) ->
  Iff (S x) (T x)

record SigmaAlgebra
  {a : Level}
  (A : Set a) :
  Set (a ⊔ lsuc lzero) where

  field
    measurable :
      Predicate A ->
      Prop

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

record OuterMeasure
  {a : Level}
  (A : Set a) :
  Set (a ⊔ lsuc lzero) where

  field
    mass :
      Predicate A ->
      ENNReal

    mass-congruent :
      (S T : Predicate A) ->
      SamePredicate S T ->
      ENNEqual (mass S) (mass T)

    mass-empty :
      IsZeroENN (mass Empty)

    mass-monotone :
      (S T : Predicate A) ->
      Subset S T ->
      ENNLE (mass S) (mass T)

    mass-countable-subadditive :
      (sets : Nat -> Predicate A) ->
      ENNLE
        (mass (CountableUnion sets))
        (countableSumENN (\ n -> mass (sets n)))

open OuterMeasure

IsCaratheodory :
  {a : Level} ->
  {A : Set a} ->
  OuterMeasure A ->
  Predicate A ->
  Prop (a ⊔ lsuc lzero)
IsCaratheodory {A = A} outer S =
  (T : Predicate A) ->
  ENNEqual
    (mass outer T)
    (sumENN
      (mass outer (Intersection T S))
      (mass outer (Difference T S)))

CaratheodoryMeasurableSpace :
  {a : Level}
  {A : Set a}
  (outer : OuterMeasure A) ->
  Prop (a ⊔ lsuc lzero)
CaratheodoryMeasurableSpace {A = A} outer =
  Exists
    (SigmaAlgebra A)
    (\ caratheodory ->
      (S : Predicate A) ->
      Iff
        (measurable caratheodory S)
        (IsCaratheodory outer S))

caratheodory-s-theorem-measure-theory :
  {a : Level} ->
  Prop (lsuc a)
caratheodory-s-theorem-measure-theory {a} =
  ExcludedMiddle lzero ->
  (A : Set a) ->
  (outer : OuterMeasure A) ->
  CaratheodoryMeasurableSpace outer
