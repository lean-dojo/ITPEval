-- Statement-only formalization of PutnamBench corpus artifact putnam_1976_b3:
-- a lower bound for the probability of the intersection of locally dependent
-- high-probability events, governed by a positive recurrence. This file contains no proof.

{-# OPTIONS --safe #-}

module Putnam1976B3 where

open import Agda.Builtin.Equality renaming (_≡_ to _==_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)

infix 4 _!=_ _<=N_ _<N_
infixr 3 _and_
infixr 2 _or_

data Bottom : Set where

record Top : Set where
  constructor top

Not : Set -> Set
Not A =
  A -> Bottom

_!=_ : {A : Set} -> A -> A -> Set
x != y =
  Not (x == y)

record _and_ (A B : Set) : Set where
  constructor both
  field
    first  : A
    second : B

data _or_ (A B : Set) : Set where
  left  : A -> A or B
  right : B -> A or B

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

data _<N_ : Nat -> Nat -> Set where
  zero<   : {n : Nat} -> zero <N suc n
  suc<suc : {m n : Nat} -> m <N n -> suc m <N suc n

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

intersection :
  {A : Set} ->
  Predicate A ->
  Predicate A ->
  Predicate A
intersection E F x =
  E x and F x

countableUnion :
  {A : Set} ->
  (Nat -> Predicate A) ->
  Predicate A
countableUnion sets x =
  Exists Nat (\ n -> sets n x)

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

record CompleteOrderedField (R : Set) : Set1 where
  field
    zeroR oneR : R
    add multiply : R -> R -> R
    negate inverse : R -> R
    lessOrEqual : R -> R -> Set
    fromNat : Nat -> R

    one-not-zero :
      oneR != zeroR

    add-commutative :
      (x y : R) -> add x y == add y x
    add-associative :
      (x y z : R) ->
      add (add x y) z == add x (add y z)
    add-zero :
      (x : R) -> add x zeroR == x
    add-inverse :
      (x : R) -> add x (negate x) == zeroR

    multiply-commutative :
      (x y : R) -> multiply x y == multiply y x
    multiply-associative :
      (x y z : R) ->
      multiply (multiply x y) z ==
      multiply x (multiply y z)
    multiply-one :
      (x : R) -> multiply x oneR == x
    multiply-zero :
      (x : R) -> multiply x zeroR == zeroR
    distribute :
      (x y z : R) ->
      multiply x (add y z) ==
      add (multiply x y) (multiply x z)
    inverse-zero :
      inverse zeroR == zeroR
    multiply-inverse :
      (x : R) ->
      x != zeroR ->
      multiply x (inverse x) == oneR

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
      lessOrEqual x y or lessOrEqual y x
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
      lessOrEqual zeroR oneR and zeroR != oneR

    fromNat-zero :
      fromNat zero == zeroR
    fromNat-successor :
      (n : Nat) ->
      fromNat (suc n) == add (fromNat n) oneR
    fromNat-addition :
      (m n : Nat) ->
      fromNat (m + n) == add (fromNat m) (fromNat n)
    fromNat-multiplication :
      (m n : Nat) ->
      fromNat (m * n) == multiply (fromNat m) (fromNat n)
    fromNat-injective :
      (m n : Nat) ->
      fromNat m == fromNat n ->
      m == n

    archimedean :
      (x : R) ->
      Exists Nat (\ n -> lessOrEqual x (fromNat n))
    least-upper-bound :
      (P : Predicate R) ->
      Exists R P ->
      Exists R
        (\ upper ->
          (x : R) ->
          P x ->
          lessOrEqual x upper) ->
      Exists R
        (\ supremum ->
          ((x : R) ->
            P x ->
            lessOrEqual x supremum)
          and
          ((upper : R) ->
            ((x : R) ->
              P x ->
              lessOrEqual x upper) ->
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

divide :
  {R : Set} ->
  CompleteOrderedField R ->
  R ->
  R ->
  R
divide reals x y =
  multiply reals x (inverse reals y)

StrictLess :
  {R : Set} ->
  CompleteOrderedField R ->
  R ->
  R ->
  Set
StrictLess reals x y =
  lessOrEqual reals x y and x != y

CloseTo :
  {R : Set} ->
  CompleteOrderedField R ->
  R ->
  R ->
  R ->
  Set
CloseTo reals center radius x =
  StrictLess reals
    (subtract reals center radius)
    x
  and
  StrictLess reals
    x
    (add reals center radius)

sumFirst :
  {R : Set} ->
  CompleteOrderedField R ->
  (Nat -> R) ->
  Nat ->
  R
sumFirst reals terms zero =
  zeroR reals
sumFirst reals terms (suc n) =
  add reals
    (sumFirst reals terms n)
    (terms n)

SequentialLimit :
  {R : Set} ->
  CompleteOrderedField R ->
  (Nat -> R) ->
  R ->
  Set
SequentialLimit reals sequence limit =
  (epsilon : _) ->
  StrictLess reals (zeroR reals) epsilon ->
  Exists Nat
    (\ cutoff ->
      (n : Nat) ->
      cutoff <=N n ->
      CloseTo reals limit epsilon (sequence n))

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

record ProbabilitySpace
  {A R : Set}
  (reals : CompleteOrderedField R)
  (events : SigmaAlgebra A) : Set1 where
  field
    probability : Predicate A -> R

    probability-congruent :
      (E F : Predicate A) ->
      ((x : A) -> Iff (E x) (F x)) ->
      probability E == probability F
    probability-empty :
      probability emptySet == zeroR reals
    probability-total :
      probability wholeSet == oneR reals
    probability-nonnegative :
      (E : Predicate A) ->
      measurable events E ->
      lessOrEqual reals (zeroR reals) (probability E)
    probability-countable-additivity :
      (sets : Nat -> Predicate A) ->
      ((n : Nat) -> measurable events (sets n)) ->
      PairwiseDisjoint sets ->
      SequentialLimit reals
        (\ count ->
          sumFirst reals
            (\ n -> probability (sets n))
            count)
        (probability (countableUnion sets))

open ProbabilitySpace

IndependentEvents :
  {A R : Set}
  {reals : CompleteOrderedField R}
  {events : SigmaAlgebra A} ->
  ProbabilitySpace reals events ->
  Predicate A ->
  Predicate A ->
  Set
IndependentEvents {reals = reals} space E F =
  probability space (intersection E F) ==
  multiply reals
    (probability space E)
    (probability space F)

Separated : Nat -> Nat -> Set
Separated i j =
  suc (suc i) <=N j or suc (suc j) <=N i

finiteIntersection :
  {A : Set} ->
  (Nat -> Predicate A) ->
  Nat ->
  Predicate A
finiteIntersection events zero =
  wholeSet
finiteIntersection events (suc n) =
  intersection
    (finiteIntersection events n)
    (events n)

oneFourth :
  {R : Set} ->
  CompleteOrderedField R ->
  R
oneFourth reals =
  divide reals
    (oneR reals)
    (fromNat reals (suc (suc (suc (suc zero)))))

putnam-1976-b3 : Set1
putnam-1976-b3 =
  (R A : Set) ->
  (reals : CompleteOrderedField R) ->
  (eventSigma : SigmaAlgebra A) ->
  (space : ProbabilitySpace reals eventSigma) ->
  (n : Nat) ->
  zero <N n ->
  (a : R) ->
  (lessOrEqual reals (zeroR reals) a
    and
    StrictLess reals a (oneFourth reals)) ->
  (u : Nat -> R) ->
  (u zero == oneR reals
    and
    u (suc zero) == subtract reals (oneR reals) a) ->
  ((k : Nat) ->
    u (suc (suc k)) ==
    subtract reals
      (u (suc k))
      (multiply reals a (u k))) ->
  ((k : Nat) ->
    StrictLess reals (zeroR reals) (u k)) ->
  (events : Nat -> Predicate A) ->
  ((i : Nat) ->
    i <N n ->
    measurable eventSigma (events i)) ->
  ((i : Nat) ->
    i <N n ->
    lessOrEqual reals
      (subtract reals (oneR reals) a)
      (probability space (events i))) ->
  ((i j : Nat) ->
    i <N n ->
    j <N n ->
    Separated i j ->
    IndependentEvents space (events i) (events j)) ->
  lessOrEqual reals
    (u n)
    (probability space (finiteIntersection events n))
