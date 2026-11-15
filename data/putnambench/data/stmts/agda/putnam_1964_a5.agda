-- Statement-only formalization of PutnamBench corpus artifact putnam_1964_a5:
-- a universal constant bounds the series of normalized reciprocal prefix sums
-- for every positive real sequence with convergent reciprocal series. This file contains no proof.

{-# OPTIONS --safe #-}

open import Agda.Builtin.Equality renaming (_≡_ to _==_)
open import Agda.Builtin.Nat using (Nat; zero; suc)

infix 4 _!=_ _<=N_
infixr 3 _and_
infixr 2 _or_

data Bottom : Set where

Not : Set -> Set
Not A = A -> Bottom

_!=_ : {A : Set} -> A -> A -> Set
x != y = Not (x == y)

record _and_ (A B : Set) : Set where
  constructor both
  field
    first  : A
    second : B

data _or_ (A B : Set) : Set where
  left  : A -> A or B
  right : B -> A or B

record Exists (A : Set) (P : A -> Set) : Set where
  constructor witness
  field
    value    : A
    property : P value

data _<=N_ : Nat -> Nat -> Set where
  zero<=   : {n : Nat} -> zero <=N n
  suc<=suc : {m n : Nat} -> m <=N n -> suc m <=N suc n

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
      (n : Nat) -> fromNat (suc n) == add (fromNat n) oneR
    fromNat-injective :
      (m n : Nat) -> fromNat m == fromNat n -> m == n

    archimedean :
      (x : R) ->
      Exists Nat (\ n -> lessOrEqual x (fromNat n))
    least-upper-bound :
      (P : R -> Set) ->
      Exists R P ->
      Exists R
        (\ upper ->
          (x : R) -> P x -> lessOrEqual x upper) ->
      Exists R
        (\ supremum ->
          ((x : R) -> P x -> lessOrEqual x supremum)
          and
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
  StrictLess reals (subtract reals center radius) x
  and
  StrictLess reals x (add reals center radius)

sumFirst :
  {R : Set} ->
  CompleteOrderedField R ->
  Nat ->
  (Nat -> R) ->
  R
sumFirst reals zero term =
  zeroR reals
sumFirst reals (suc n) term =
  add reals
    (sumFirst reals n term)
    (term n)

ConvergesTo :
  {R : Set} ->
  CompleteOrderedField R ->
  (Nat -> R) ->
  R ->
  Set
ConvergesTo reals sequence limit =
  (epsilon : _) ->
  StrictLess reals (zeroR reals) epsilon ->
  Exists Nat
    (\ cutoff ->
      (n : Nat) ->
      cutoff <=N n ->
      CloseTo reals limit epsilon (sequence n))

SeriesHasSum :
  {R : Set} ->
  CompleteOrderedField R ->
  (Nat -> R) ->
  R ->
  Set
SeriesHasSum reals term limit =
  ConvergesTo reals
    (\ n -> sumFirst reals n term)
    limit

PositiveSequence :
  {R : Set} ->
  CompleteOrderedField R ->
  (Nat -> R) ->
  Set
PositiveSequence reals a =
  (n : Nat) ->
  StrictLess reals (zeroR reals) (a n)

reciprocalTerm :
  {R : Set} ->
  CompleteOrderedField R ->
  (Nat -> R) ->
  Nat ->
  R
reciprocalTerm reals a n =
  divide reals (oneR reals) (a n)

weightedPrefixTerm :
  {R : Set} ->
  CompleteOrderedField R ->
  (Nat -> R) ->
  Nat ->
  R
weightedPrefixTerm reals a n =
  divide reals
    (fromNat reals (suc n))
    (sumFirst reals (suc n) a)

module Putnam1964A5Statement
  {R : Set}
  (reals : CompleteOrderedField R) where

  Admissible :
    (Nat -> R) ->
    Set
  Admissible a =
    PositiveSequence reals a
    and
    Exists R
      (\ reciprocalSum ->
        SeriesHasSum reals
          (reciprocalTerm reals a)
          reciprocalSum)

  BoundHolds :
    R ->
    (Nat -> R) ->
    Set
  BoundHolds k a =
    Exists R
      (\ reciprocalSum ->
        SeriesHasSum reals
          (reciprocalTerm reals a)
          reciprocalSum
        and
        Exists R
          (\ weightedSum ->
            SeriesHasSum reals
              (weightedPrefixTerm reals a)
              weightedSum
            and
            lessOrEqual reals
              weightedSum
              (multiply reals k reciprocalSum)))

  proposition : Set
  proposition =
    Exists R
      (\ k ->
        (a : Nat -> R) ->
        Admissible a ->
        BoundHolds k a)

putnam-1964-a5 : Set1
putnam-1964-a5 =
  (R : Set) ->
  (reals : CompleteOrderedField R) ->
  Putnam1964A5Statement.proposition reals
