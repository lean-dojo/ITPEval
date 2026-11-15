-- Statement-only formalization of PutnamBench corpus artifact putnam_1968_b1:
-- the probability that the minimum of two finite-range integer-valued random
-- variables equals k is p1 + p2 minus the probability that their maximum
-- equals k. This file contains no proof.

{-# OPTIONS --safe #-}

open import Agda.Builtin.Equality renaming (_≡_ to _==_)
open import Agda.Builtin.Int using (Int; pos; negsuc)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)

infix 4 _!=_ _<=N_

data Bottom : Set where

record Top : Set where
  constructor top

Not : Set -> Set
Not A =
  A -> Bottom

_!=_ : {A : Set} -> A -> A -> Set
x != y =
  Not (x == y)

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

data _<=N_ : Nat -> Nat -> Set where
  zero<=   : {n : Nat} -> zero <=N n
  suc<=suc : {m n : Nat} -> m <=N n -> suc m <=N suc n

data List (A : Set) : Set where
  empty : List A
  cons  : A -> List A -> List A

data Member {A : Set} (x : A) : List A -> Set where
  at-head : {xs : List A} -> Member x (cons x xs)
  in-tail :
    {y : A} ->
    {xs : List A} ->
    Member x xs ->
    Member x (cons y xs)

natMinimum : Nat -> Nat -> Nat
natMinimum zero n =
  zero
natMinimum (suc m) zero =
  zero
natMinimum (suc m) (suc n) =
  suc (natMinimum m n)

natMaximum : Nat -> Nat -> Nat
natMaximum zero n =
  n
natMaximum (suc m) zero =
  suc m
natMaximum (suc m) (suc n) =
  suc (natMaximum m n)

integerMinimum : Int -> Int -> Int
integerMinimum (pos m) (pos n) =
  pos (natMinimum m n)
integerMinimum (pos m) (negsuc n) =
  negsuc n
integerMinimum (negsuc m) (pos n) =
  negsuc m
integerMinimum (negsuc m) (negsuc n) =
  negsuc (natMaximum m n)

integerMaximum : Int -> Int -> Int
integerMaximum (pos m) (pos n) =
  pos (natMaximum m n)
integerMaximum (pos m) (negsuc n) =
  pos m
integerMaximum (negsuc m) (pos n) =
  pos n
integerMaximum (negsuc m) (negsuc n) =
  negsuc (natMinimum m n)

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
    fromNat-addition :
      (m n : Nat) ->
      fromNat (m + n) == add (fromNat m) (fromNat n)
    fromNat-multiplication :
      (m n : Nat) ->
      fromNat (m * n) == multiply (fromNat m) (fromNat n)
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
          (x : R) ->
          P x ->
          lessOrEqual x upper) ->
      Exists R
        (\ supremum ->
          Both
            ((x : R) -> P x -> lessOrEqual x supremum)
            ((upper : R) ->
              ((x : R) -> P x -> lessOrEqual x upper) ->
              lessOrEqual supremum upper))

open CompleteOrderedField

subtract :
  {R : Set} ->
  CompleteOrderedField R ->
  R ->
  R ->
  R
subtract reals x y =
  add reals x (negate reals y)

StrictLess :
  {R : Set} ->
  CompleteOrderedField R ->
  R ->
  R ->
  Set
StrictLess reals x y =
  Both (lessOrEqual reals x y) (x != y)

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
        (absoluteValue reals (subtract reals (sequence n) limit))
        epsilon)

sumFirst :
  {R : Set} ->
  CompleteOrderedField R ->
  (Nat -> R) ->
  Nat ->
  R
sumFirst reals term zero =
  zeroR reals
sumFirst reals term (suc n) =
  add reals (sumFirst reals term n) (term n)

Predicate : Set -> Set1
Predicate A =
  A -> Set

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

PairwiseDisjoint :
  {A : Set} ->
  (Nat -> Predicate A) ->
  Set
PairwiseDisjoint {A} sets =
  (i j : Nat) ->
  i != j ->
  (x : A) ->
  sets i x ->
  sets j x ->
  Bottom

record Measure
  {A R : Set}
  (reals : CompleteOrderedField R)
  (events : SigmaAlgebra A) : Set1 where
  field
    mass : Predicate A -> R

    mass-congruent :
      (E F : Predicate A) ->
      ((x : A) -> Iff (E x) (F x)) ->
      mass E == mass F
    mass-empty :
      mass emptySet == zeroR reals
    mass-nonnegative :
      (E : Predicate A) ->
      measurable events E ->
      lessOrEqual reals (zeroR reals) (mass E)
    countable-additivity :
      (sets : Nat -> Predicate A) ->
      ((n : Nat) -> measurable events (sets n)) ->
      PairwiseDisjoint sets ->
      SequentialLimit reals
        (\ count -> sumFirst reals (\ n -> mass (sets n)) count)
        (mass (countableUnion sets))

open Measure

record ProbabilitySpace
  {A R : Set}
  (reals : CompleteOrderedField R)
  (events : SigmaAlgebra A) : Set1 where
  field
    measure : Measure reals events
    total-mass-one :
      mass measure wholeSet == oneR reals

open ProbabilitySpace

probabilityOf :
  {A R : Set}
  {reals : CompleteOrderedField R}
  {events : SigmaAlgebra A} ->
  ProbabilitySpace reals events ->
  Predicate A ->
  R
probabilityOf space E =
  mass (measure space) E

preimage :
  {A B : Set} ->
  (A -> B) ->
  Predicate B ->
  Predicate A
preimage f E x =
  E (f x)

MeasurableIntegerFunction :
  {A : Set} ->
  SigmaAlgebra A ->
  (A -> Int) ->
  Set1
MeasurableIntegerFunction events f =
  (E : Predicate Int) ->
  measurable events (preimage f E)

FiniteImage :
  {A : Set} ->
  (A -> Int) ->
  Set
FiniteImage {A} f =
  Exists (List Int)
    (\ values ->
      (x : A) ->
      Member (f x) values)

equalEvent :
  {A : Set} ->
  (A -> Int) ->
  Int ->
  Predicate A
equalEvent f k x =
  f x == k

minimumEvent :
  {A : Set} ->
  (A -> Int) ->
  (A -> Int) ->
  Int ->
  Predicate A
minimumEvent X Y k x =
  integerMinimum (X x) (Y x) == k

maximumEvent :
  {A : Set} ->
  (A -> Int) ->
  (A -> Int) ->
  Int ->
  Predicate A
maximumEvent X Y k x =
  integerMaximum (X x) (Y x) == k

putnam1968B1Solution :
  {R : Set} ->
  CompleteOrderedField R ->
  R ->
  R ->
  R ->
  R
putnam1968B1Solution reals p1 p2 p3 =
  subtract reals (add reals p1 p2) p3

putnam-1968-b1 : Set1
putnam-1968-b1 =
  (R : Set) ->
  (Omega : Set) ->
  (reals : CompleteOrderedField R) ->
  (events : SigmaAlgebra Omega) ->
  (space : ProbabilitySpace reals events) ->
  (X Y : Omega -> Int) ->
  MeasurableIntegerFunction events X ->
  MeasurableIntegerFunction events Y ->
  FiniteImage X ->
  FiniteImage Y ->
  (k : Int) ->
  probabilityOf space (minimumEvent X Y k) ==
  putnam1968B1Solution reals
    (probabilityOf space (equalEvent X k))
    (probabilityOf space (equalEvent Y k))
    (probabilityOf space (maximumEvent X Y k))
