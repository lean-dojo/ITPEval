-- Statement-only formalization of PutnamBench corpus artifact putnam_1964_a3:
-- an injective dense sequence in (0,1) determines adjacent left and right
-- gaps whose cubic products have infinite sum 1/3. This file contains no proof.

{-# OPTIONS --safe #-}

open import Agda.Builtin.Equality renaming (_≡_ to _==_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)

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

NatStrictLess : Nat -> Nat -> Set
NatStrictLess m n =
  suc m <=N n

three : Nat
three =
  suc (suc (suc zero))

record CompleteOrderedField (R : Set) : Set1 where
  field
    zeroR oneR : R
    add multiply : R -> R -> R
    negate inverse : R -> R
    lessOrEqual : R -> R -> Set
    fromNat : Nat -> R
    supremum infimum : (R -> Set) -> R

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
    fromNat-addition :
      (m n : Nat) ->
      fromNat (m + n) == add (fromNat m) (fromNat n)
    fromNat-multiplication :
      (m n : Nat) ->
      fromNat (m * n) == multiply (fromNat m) (fromNat n)
    fromNat-injective :
      (m n : Nat) -> fromNat m == fromNat n -> m == n

    archimedean :
      (x : R) ->
      Exists Nat (\ n -> lessOrEqual x (fromNat n))

    supremum-property :
      (P : R -> Set) ->
      Exists R P ->
      Exists R
        (\ upper ->
          (x : R) -> P x -> lessOrEqual x upper) ->
      ((x : R) ->
        P x ->
        lessOrEqual x (supremum P))
      and
      ((upper : R) ->
        ((x : R) -> P x -> lessOrEqual x upper) ->
        lessOrEqual (supremum P) upper)

    infimum-property :
      (P : R -> Set) ->
      Exists R P ->
      Exists R
        (\ lower ->
          (x : R) -> P x -> lessOrEqual lower x) ->
      ((x : R) ->
        P x ->
        lessOrEqual (infimum P) x)
      and
      ((lower : R) ->
        ((x : R) -> P x -> lessOrEqual lower x) ->
        lessOrEqual lower (infimum P))

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

Injective :
  {A B : Set} ->
  (A -> B) ->
  Set
Injective f =
  (i j : _) ->
  f i == f j ->
  i == j

DenseInOpenUnitInterval :
  {R : Set} ->
  CompleteOrderedField R ->
  (Nat -> R) ->
  Set
DenseInOpenUnitInterval {R} reals x =
  ((n : Nat) ->
    StrictLess reals (zeroR reals) (x n)
    and
    StrictLess reals (x n) (oneR reals))
  and
  ((y : R) ->
    StrictLess reals (zeroR reals) y ->
    StrictLess reals y (oneR reals) ->
    (lower upper : R) ->
    StrictLess reals lower y ->
    StrictLess reals y upper ->
    Exists Nat
      (\ n ->
        StrictLess reals lower (x n)
        and
        StrictLess reals (x n) upper))

LeftCandidate :
  {R : Set} ->
  CompleteOrderedField R ->
  (Nat -> R) ->
  Nat ->
  R ->
  Set
LeftCandidate reals x n p =
  p == zeroR reals
  or
  (StrictLess reals p (x n)
  and
  Exists Nat
    (\ i ->
      NatStrictLess i n
      and
      p == x i))

RightCandidate :
  {R : Set} ->
  CompleteOrderedField R ->
  (Nat -> R) ->
  Nat ->
  R ->
  Set
RightCandidate reals x n p =
  p == oneR reals
  or
  (StrictLess reals (x n) p
  and
  Exists Nat
    (\ i ->
      NatStrictLess i n
      and
      p == x i))

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
ConvergesTo {R} reals sequence limit =
  (epsilon : R) ->
  StrictLess reals (zeroR reals) epsilon ->
  Exists Nat
    (\ cutoff ->
      (n : Nat) ->
      cutoff <=N n ->
      StrictLess reals
        (subtract reals limit epsilon)
        (sequence n)
      and
      StrictLess reals
        (sequence n)
        (add reals limit epsilon))

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

module Putnam1964A3Statement
  {R : Set}
  (reals : CompleteOrderedField R) where

  summand :
    (Nat -> R) ->
    (Nat -> R) ->
    Nat ->
    R
  summand a b n =
    multiply reals
      (multiply reals (a n) (b n))
      (add reals (a n) (b n))

  proposition : Set
  proposition =
    (x a b : Nat -> R) ->
    DenseInOpenUnitInterval reals x ->
    Injective x ->
    ((n : Nat) ->
      a n ==
      subtract reals
        (x n)
        (supremum reals (LeftCandidate reals x n))) ->
    ((n : Nat) ->
      b n ==
      subtract reals
        (infimum reals (RightCandidate reals x n))
        (x n)) ->
    SeriesHasSum reals
      (summand a b)
      (divide reals
        (oneR reals)
        (fromNat reals three))

putnam-1964-a3 : Set1
putnam-1964-a3 =
  (R : Set) ->
  (reals : CompleteOrderedField R) ->
  Putnam1964A3Statement.proposition reals
