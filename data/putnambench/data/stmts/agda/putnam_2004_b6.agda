-- Statement-only formalization of PutnamBench corpus artifact putnam_2004_b6
-- (putnambench__agda__putnam_2004_b6): a positive-integer set whose positive
-- difference set has unbounded successive gaps has asymptotic density zero.
-- This file contains no proof.

{-# OPTIONS --safe #-}

module Putnam2004B6 where

open import Agda.Builtin.Equality renaming (_≡_ to _==_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _-_; _*_)

infix 4 _!=_ _<=N_ _<N_
infixr 3 _and_
infixr 2 _or_

data Bottom : Set where

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
  zero<=N   : {n : Nat} -> zero <=N n
  suc<=sucN : {m n : Nat} -> m <=N n -> suc m <=N suc n

_<N_ : Nat -> Nat -> Set
m <N n =
  suc m <=N n

data Fin : Nat -> Set where
  fzero : {n : Nat} -> Fin (suc n)
  fsuc  : {n : Nat} -> Fin n -> Fin (suc n)

Predicate : Set -> Set1
Predicate A =
  A -> Set

record HasCardinality
  {A : Set}
  (S : Predicate A)
  (cardinality : Nat) :
  Set where

  field
    enumerate :
      Fin cardinality ->
      A

    enumerated-member :
      (i : Fin cardinality) ->
      S (enumerate i)

    enumeration-complete :
      (x : A) ->
      S x ->
      Exists (Fin cardinality)
        (\ i -> x == enumerate i)

    enumeration-injective :
      (i j : Fin cardinality) ->
      enumerate i == enumerate j ->
      i == j

record CompleteOrderedRealField (R : Set) : Set1 where
  field
    zeroR oneR : R
    add multiply : R -> R -> R
    negate inverse : R -> R
    lessOrEqual : R -> R -> Set
    fromNat : Nat -> R

    one-not-zero :
      oneR != zeroR

    add-commutative :
      (x y : R) ->
      add x y == add y x
    add-associative :
      (x y z : R) ->
      add (add x y) z == add x (add y z)
    add-zero :
      (x : R) ->
      add x zeroR == x
    add-inverse :
      (x : R) ->
      add x (negate x) == zeroR

    multiply-commutative :
      (x y : R) ->
      multiply x y == multiply y x
    multiply-associative :
      (x y z : R) ->
      multiply (multiply x y) z ==
      multiply x (multiply y z)
    multiply-one :
      (x : R) ->
      multiply x oneR == x
    multiply-zero :
      (x : R) ->
      multiply x zeroR == zeroR
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
      (x : R) ->
      lessOrEqual x x
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
      Exists Nat
        (\ n -> lessOrEqual x (fromNat n))

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
          ((x : R) ->
            P x ->
            lessOrEqual x supremum)
          and
          ((upper : R) ->
            ((x : R) ->
              P x ->
              lessOrEqual x upper) ->
            lessOrEqual supremum upper))

open CompleteOrderedRealField

subtract :
  {R : Set} ->
  CompleteOrderedRealField R ->
  R ->
  R ->
  R
subtract reals x y =
  add reals x (negate reals y)

divide :
  {R : Set} ->
  CompleteOrderedRealField R ->
  R ->
  R ->
  R
divide reals x y =
  multiply reals x (inverse reals y)

StrictLess :
  {R : Set} ->
  CompleteOrderedRealField R ->
  R ->
  R ->
  Set
StrictLess reals x y =
  lessOrEqual reals x y and x != y

CloseTo :
  {R : Set} ->
  CompleteOrderedRealField R ->
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

LimitAtPositiveInfinity :
  {R : Set} ->
  CompleteOrderedRealField R ->
  (R -> R) ->
  R ->
  Set
LimitAtPositiveInfinity {R} reals function limit =
  (epsilon : R) ->
  StrictLess reals (zeroR reals) epsilon ->
  Exists R
    (\ threshold ->
      (x : R) ->
      lessOrEqual reals threshold x ->
      CloseTo reals limit epsilon (function x))

Positive : Nat -> Set
Positive n =
  zero <N n

module Putnam2004B6Statement
  {R : Set}
  (reals : CompleteOrderedRealField R) where

  CountsAtMost :
    Predicate Nat ->
    (R -> Nat) ->
    Set
  CountsAtMost A N =
    (x : R) ->
    HasCardinality
      (\ a ->
        A a
        and
        lessOrEqual reals (fromNat reals a) x)
      (N x)

  IsPositiveDifferenceSet :
    Predicate Nat ->
    Predicate Nat ->
    Set
  IsPositiveDifferenceSet A B =
    (d : Nat) ->
    Iff
      (B d)
      (Positive d
      and
      Exists Nat
        (\ a ->
          A a
          and
          Exists Nat
            (\ aPrime ->
              A aPrime
              and
              d == a - aPrime)))

  IsIncreasingEnumeration :
    Predicate Nat ->
    (Nat -> Nat) ->
    Set
  IsIncreasingEnumeration B b =
    ((d : Nat) ->
      Iff
        (B d)
        (Exists Nat (\ i -> b i == d)))
    and
    ((i : Nat) ->
      b i <N b (suc i))

  HasUnboundedGaps :
    (Nat -> Nat) ->
    Set
  HasUnboundedGaps b =
    (r : Nat) ->
    Exists Nat
      (\ i ->
        r <=N (b (suc i) - b i))

  proposition : Set1
  proposition =
    (A B : Predicate Nat) ->
    (N : R -> Nat) ->
    (b : Nat -> Nat) ->
    Exists Nat A ->
    ((a : Nat) -> A a -> Positive a) ->
    CountsAtMost A N ->
    IsPositiveDifferenceSet A B ->
    IsIncreasingEnumeration B b ->
    HasUnboundedGaps b ->
    LimitAtPositiveInfinity reals
      (\ x ->
        divide reals
          (fromNat reals (N x))
          x)
      (zeroR reals)

putnam-2004-b6 : Set1
putnam-2004-b6 =
  (R : Set) ->
  (reals : CompleteOrderedRealField R) ->
  Putnam2004B6Statement.proposition reals
