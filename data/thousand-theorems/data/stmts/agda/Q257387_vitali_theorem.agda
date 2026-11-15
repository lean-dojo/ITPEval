-- Statement-only formalization of thousand-theorems corpus artifact Q257387,
-- "Vitali theorem": the quotient-selected Vitali subset of the fixed real
-- unit interval is not Borel measurable. This file contains no proof.

{-# OPTIONS --safe #-}

module Q257387_vitali_theorem where

open import Agda.Primitive using (Level; lzero; lsuc; _⊔_)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat; zero; suc)

data Bottom {p : Level} : Set p where

Not :
  {p : Level} ->
  Set p ->
  Set p
Not {p} A =
  A -> Bottom {p}

record Both
  {p q : Level}
  (A : Set p)
  (B : Set q) :
  Set (p ⊔ q) where

  constructor both
  field
    first  : A
    second : B

record Iff
  {p q : Level}
  (A : Set p)
  (B : Set q) :
  Set (p ⊔ q) where

  constructor equivalence
  field
    forward  : A -> B
    backward : B -> A

data Either
  {p q : Level}
  (A : Set p)
  (B : Set q) :
  Set (p ⊔ q) where

  left  : A -> Either A B
  right : B -> Either A B

data Exists
  {a p : Level}
  (A : Set a)
  (P : A -> Set p) :
  Set (a ⊔ p) where

  witness :
    (value : A) ->
    P value ->
    Exists A P

infix 4 _==N_ _<=N_ _<N_
infixl 6 _+N_
infixl 7 _*N_

data _==N_ : Nat -> Nat -> Set where
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

data _<=N_ : Nat -> Nat -> Set where
  zero<=   : {n : Nat} -> zero <=N n
  suc<=suc : {m n : Nat} -> m <=N n -> suc m <=N suc n

_<N_ : Nat -> Nat -> Set
m <N n =
  suc m <=N n

-- Rationals are integer numerators over positive denominators.  The
-- equality and order relations quotient this concrete presentation.
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

negateQ : Rational -> Rational
negateQ q =
  rational
    (negativePart q)
    (positivePart q)
    (denominatorCode q)

subtractQ : Rational -> Rational -> Rational
subtractQ q r =
  addQ q (negateQ r)

RationalEqual : Rational -> Rational -> Set
RationalEqual q r =
  ((positivePart q *N denominatorValue r) +N
   (negativePart r *N denominatorValue q))
  ==N
  ((positivePart r *N denominatorValue q) +N
   (negativePart q *N denominatorValue r))

RationalLT : Rational -> Rational -> Set
RationalLT q r =
  ((positivePart q *N denominatorValue r) +N
   (negativePart r *N denominatorValue q))
  <N
  ((positivePart r *N denominatorValue q) +N
   (negativePart q *N denominatorValue r))

-- The real line is fixed internally as the type of finite located lower
-- Dedekind cuts of the rationals.
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

RealEqual : DedekindReal -> DedekindReal -> Set
RealEqual x y =
  (q : Rational) ->
  Iff (lower x q) (lower y q)

RealLess : DedekindReal -> DedekindReal -> Set
RealLess x y =
  Exists Rational
    (\ q ->
      Both
        (Not (lower x q))
        (lower y q))

-- This says exactly that x - y is the image of a rational: if x = y + c,
-- then q < x precisely when q - c < y.
RationalDifference : DedekindReal -> DedekindReal -> Set
RationalDifference x y =
  Exists Rational
    (\ c ->
      (q : Rational) ->
      Iff
        (lower x q)
        (lower y (subtractQ q c)))

InUnitInterval : DedekindReal -> Set
InUnitInterval x =
  Both
    ((q : Rational) ->
      RationalLT q zeroQ ->
      lower x q)
    ((q : Rational) ->
      lower x q ->
      RationalLT q oneQ)

record UnitPoint : Set1 where
  constructor unit-point
  field
    realValue :
      DedekindReal

    liesInUnitInterval :
      InUnitInterval realValue

open UnitPoint

VitaliRelated : UnitPoint -> UnitPoint -> Set
VitaliRelated x y =
  RationalDifference (realValue x) (realValue y)

-- Safe Agda has no native quotient type.  This record is an exact quotient
-- presentation of [0,1] by rational difference, together with the
-- representative selector corresponding to Lean's vT, vRep, and vRep_spec.
-- The Vitali set below is derived from this selector rather than supplied as
-- an external transversal, and the final proposition binds the selector
-- internally.
record VitaliQuotientSelection : Set2 where
  field
    Class :
      Set1

    classOf :
      UnitPoint ->
      Class

    classOf-equality :
      (x y : UnitPoint) ->
      Iff
        (classOf x ≡ classOf y)
        (VitaliRelated x y)

    representative :
      Class ->
      UnitPoint

    representative-class :
      (class : Class) ->
      classOf (representative class) ≡ class

open VitaliQuotientSelection

Predicate :
  {a : Level} ->
  Set a ->
  Set (lsuc a)
Predicate {a} A =
  A -> Set a

Empty :
  {a : Level} ->
  {A : Set a} ->
  Predicate A
Empty {a} _ =
  Bottom {a}

Complement :
  {a : Level} ->
  {A : Set a} ->
  Predicate A ->
  Predicate A
Complement S x =
  Not (S x)

CountableUnion :
  {a : Level} ->
  {A : Set a} ->
  (Nat -> Predicate A) ->
  Predicate A
CountableUnion sets x =
  Exists Nat (\ n -> sets n x)

SamePredicate :
  {a : Level} ->
  {A : Set a} ->
  Predicate A ->
  Predicate A ->
  Set a
SamePredicate {A = A} S T =
  (x : A) ->
  Iff (S x) (T x)

OrderOpen :
  Predicate DedekindReal ->
  Set1
OrderOpen U =
  (x : DedekindReal) ->
  U x ->
  Exists DedekindReal
    (\ lowerBound ->
      Exists DedekindReal
        (\ upperBound ->
          Both
            (RealLess lowerBound x)
            (Both
              (RealLess x upperBound)
              ((y : DedekindReal) ->
                RealLess lowerBound y ->
                RealLess y upperBound ->
                U y))))

-- This is the Borel sigma-algebra generated by the order topology of the
-- fixed Dedekind real line.  It is the target counterpart of Lean's
-- MeasureTheory.MeasurableSet on ℝ.
data MeasurableSet :
  Predicate DedekindReal ->
  Set2 where

  measurable-open :
    {U : Predicate DedekindReal} ->
    OrderOpen U ->
    MeasurableSet U

  measurable-empty :
    MeasurableSet Empty

  measurable-complement :
    {S : Predicate DedekindReal} ->
    MeasurableSet S ->
    MeasurableSet (Complement S)

  measurable-countable-union :
    (sets : Nat -> Predicate DedekindReal) ->
    ((n : Nat) -> MeasurableSet (sets n)) ->
    MeasurableSet (CountableUnion sets)

  measurable-congruent :
    {S T : Predicate DedekindReal} ->
    SamePredicate S T ->
    MeasurableSet S ->
    MeasurableSet T

vitaliSet :
  VitaliQuotientSelection ->
  Predicate DedekindReal
vitaliSet selection x =
  Exists
    (Class selection)
    (\ class ->
      RealEqual
        (realValue (representative selection class))
        x)

vitaliSet-not-measurable : Set2
vitaliSet-not-measurable =
  (selection : VitaliQuotientSelection) ->
  Not (MeasurableSet (vitaliSet selection))
