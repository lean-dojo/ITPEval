-- Statement-only formalization of thousand-theorems corpus artifact Q1568811,
-- "Hahn decomposition theorem": every countably additive signed measure
-- valued in a fixed Cauchy-sequence representation of the real numbers admits
-- complementary measurable positive and negative sets. This file contains no
-- proof.

{-# OPTIONS --safe --prop #-}

module Q1568811_hahn_decomposition_theorem where

open import Agda.Primitive using (Level; lzero; lsuc; _⊔_; Prop)
open import Agda.Builtin.Nat using (Nat; zero; suc)

data Bottom {p : Level} : Prop p where

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

_!=N_ :
  Nat ->
  Nat ->
  Prop
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

-- A rational is an integer numerator, represented as a difference of
-- naturals, divided by a positive denominator. The order below identifies
-- extensionally equal presentations by cross multiplication.
record Rational : Set where
  constructor rational
  field
    positivePart    : Nat
    negativePart    : Nat
    denominatorCode : Nat

open Rational

denominatorValue :
  Rational ->
  Nat
denominatorValue q =
  suc (denominatorCode q)

denominatorProductCode :
  Nat ->
  Nat ->
  Nat
denominatorProductCode d e =
  d +N (e +N (d *N e))

zeroQ :
  Rational
zeroQ =
  rational zero zero zero

negateQ :
  Rational ->
  Rational
negateQ q =
  rational
    (negativePart q)
    (positivePart q)
    (denominatorCode q)

addQ :
  Rational ->
  Rational ->
  Rational
addQ q r =
  rational
    ((positivePart q *N denominatorValue r) +N
     (positivePart r *N denominatorValue q))
    ((negativePart q *N denominatorValue r) +N
     (negativePart r *N denominatorValue q))
    (denominatorProductCode
      (denominatorCode q)
      (denominatorCode r))

RationalLE :
  Rational ->
  Rational ->
  Prop
RationalLE q r =
  ((positivePart q *N denominatorValue r) +N
   (negativePart r *N denominatorValue q))
  <=N
  ((positivePart r *N denominatorValue q) +N
   (negativePart q *N denominatorValue r))

unitFraction :
  Nat ->
  Rational
unitFraction precision =
  rational (suc zero) zero precision

RationalWithin :
  Rational ->
  Rational ->
  Rational ->
  Prop
RationalWithin epsilon q r =
  Both
    (RationalLE q (addQ r epsilon))
    (RationalLE r (addQ q epsilon))

-- This is a fixed presentation of the real numbers by rational Cauchy
-- sequences. All real operations below are extensional relations, so distinct
-- Cauchy representatives of the same real number are identified.
IsCauchy :
  (Nat -> Rational) ->
  Prop
IsCauchy sequence =
  (precision : Nat) ->
  Exists Nat
    (\ cutoff ->
      (m n : Nat) ->
      cutoff <=N m ->
      cutoff <=N n ->
      RationalWithin
        (unitFraction precision)
        (sequence m)
        (sequence n))

record Real : Set where
  field
    approximation :
      Nat ->
      Rational

    cauchy :
      IsCauchy approximation

open Real

RealWithinAt :
  Nat ->
  Real ->
  Real ->
  Prop
RealWithinAt precision x y =
  Exists Nat
    (\ cutoff ->
      (i j : Nat) ->
      cutoff <=N i ->
      cutoff <=N j ->
      RationalWithin
        (unitFraction precision)
        (approximation x i)
        (approximation y j))

RealEquivalent :
  Real ->
  Real ->
  Prop
RealEquivalent x y =
  (precision : Nat) ->
  RealWithinAt precision x y

RealLE :
  Real ->
  Real ->
  Prop
RealLE x y =
  (precision : Nat) ->
  Exists Nat
    (\ cutoff ->
      (i j : Nat) ->
      cutoff <=N i ->
      cutoff <=N j ->
      RationalLE
        (approximation x i)
        (addQ
          (approximation y j)
          (unitFraction precision)))

RealZero :
  Real ->
  Prop
RealZero x =
  (precision : Nat) ->
  Exists Nat
    (\ cutoff ->
      (i : Nat) ->
      cutoff <=N i ->
      RationalWithin
        (unitFraction precision)
        (approximation x i)
        zeroQ)

RealNonnegative :
  Real ->
  Prop
RealNonnegative x =
  (precision : Nat) ->
  Exists Nat
    (\ cutoff ->
      (i : Nat) ->
      cutoff <=N i ->
      RationalLE
        (negateQ (unitFraction precision))
        (approximation x i))

RealNonpositive :
  Real ->
  Prop
RealNonpositive x =
  (precision : Nat) ->
  Exists Nat
    (\ cutoff ->
      (i : Nat) ->
      cutoff <=N i ->
      RationalLE
        (approximation x i)
        (unitFraction precision))

RealAdd :
  Real ->
  Real ->
  Real ->
  Prop
RealAdd x y sum =
  (precision : Nat) ->
  Exists Nat
    (\ cutoff ->
      (i j k : Nat) ->
      cutoff <=N i ->
      cutoff <=N j ->
      cutoff <=N k ->
      RationalWithin
        (unitFraction precision)
        (approximation sum k)
        (addQ
          (approximation x i)
          (approximation y j)))

RealConverges :
  (Nat -> Real) ->
  Real ->
  Prop
RealConverges sequence limit =
  (precision : Nat) ->
  Exists Nat
    (\ cutoff ->
      (n : Nat) ->
      cutoff <=N n ->
      RealWithinAt precision (sequence n) limit)

RealHasSum :
  (Nat -> Real) ->
  Real ->
  Prop
RealHasSum terms total =
  Exists (Nat -> Real)
    (\ partialSums ->
      Both
        (RealZero (partialSums zero))
        (Both
          ((n : Nat) ->
            RealAdd
              (partialSums n)
              (terms n)
              (partialSums (suc n)))
          (RealConverges partialSums total)))

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

PairwiseDisjoint :
  {a : Level} ->
  {A : Set a} ->
  (Nat -> Predicate A) ->
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

record SignedMeasure
  {a : Level}
  {A : Set a}
  (events : SigmaAlgebra A) :
  Set (a ⊔ lsuc lzero) where

  field
    mass :
      Predicate A ->
      Real

    mass-congruent :
      (S T : Predicate A) ->
      SamePredicate S T ->
      RealEquivalent (mass S) (mass T)

    mass-empty :
      RealZero (mass Empty)

    measurable-countable-additivity :
      (sets : Nat -> Predicate A) ->
      ((n : Nat) -> measurable events (sets n)) ->
      PairwiseDisjoint sets ->
      RealHasSum
        (\ n -> mass (sets n))
        (mass (CountableUnion sets))

open SignedMeasure

PositiveOn :
  {a : Level} ->
  {A : Set a} ->
  (events : SigmaAlgebra A) ->
  SignedMeasure events ->
  Predicate A ->
  Prop (a ⊔ lsuc lzero)
PositiveOn {A = A} events signed S =
  (T : Predicate A) ->
  measurable events T ->
  Subset T S ->
  RealNonnegative (mass signed T)

NegativeOn :
  {a : Level} ->
  {A : Set a} ->
  (events : SigmaAlgebra A) ->
  SignedMeasure events ->
  Predicate A ->
  Prop (a ⊔ lsuc lzero)
NegativeOn {A = A} events signed S =
  (T : Predicate A) ->
  measurable events T ->
  Subset T S ->
  RealNonpositive (mass signed T)

record IsComplementary
  {a : Level}
  {A : Set a}
  (S T : Predicate A) :
  Prop (a ⊔ lsuc lzero) where

  field
    disjoint :
      (x : A) ->
      S x ->
      T x ->
      Bottom {a}

    covers :
      (x : A) ->
      Either (S x) (T x)

hahn-decomposition-theorem :
  {a : Level} ->
  Prop (lsuc a)
hahn-decomposition-theorem {a} =
  (A : Set a) ->
  (events : SigmaAlgebra A) ->
  (signed : SignedMeasure events) ->
  Exists (Predicate A)
    (\ positiveSet ->
      Exists (Predicate A)
        (\ negativeSet ->
          Both
            (measurable events positiveSet)
            (Both
              (PositiveOn events signed positiveSet)
              (Both
                (measurable events negativeSet)
                (Both
                  (NegativeOn events signed negativeSet)
                  (IsComplementary positiveSet negativeSet))))))
