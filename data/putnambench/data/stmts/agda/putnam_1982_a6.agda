-- Statement-only formalization of PutnamBench corpus artifact putnam_1982_a6:
-- the proposed preservation of a convergent real series under permutations
-- with decreasing term magnitudes and vanishing displacement-weighted terms
-- is false. This file contains no proof.

{-# OPTIONS --safe #-}

open import Agda.Builtin.Equality renaming (_≡_ to _==_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)

infix 4 _!=_ _<=N_
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

NatStrictLess : Nat -> Nat -> Set
NatStrictLess m n =
  suc m <=N n

oneN : Nat
oneN =
  suc zero

Positive : Nat -> Set
Positive n =
  oneN <=N n

record PositiveBijection (b : Nat -> Nat) : Set where
  field
    maps-positive :
      (n : Nat) ->
      Positive n ->
      Positive (b n)

    injective-on-positive :
      (m n : Nat) ->
      Positive m ->
      Positive n ->
      b m == b n ->
      m == n

    surjective-on-positive :
      (n : Nat) ->
      Positive n ->
      Exists Nat
        (\ m ->
          Positive m
          and
          b m == n)

record CompleteOrderedRealField (R : Set) : Set1 where
  field
    zeroR oneR : R
    add multiply : R -> R -> R
    negate inverse absoluteValue : R -> R
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

    absolute-nonnegative :
      (x : R) ->
      lessOrEqual zeroR (absoluteValue x)
    absolute-of-nonnegative :
      (x : R) ->
      lessOrEqual zeroR x ->
      absoluteValue x == x
    absolute-of-nonpositive :
      (x : R) ->
      lessOrEqual x zeroR ->
      absoluteValue x == negate x

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
        (\ n ->
          lessOrEqual x (fromNat n))
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

ConvergesTo :
  {R : Set} ->
  CompleteOrderedRealField R ->
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
      CloseTo reals limit epsilon (sequence n))

sumFromOneThrough :
  {R : Set} ->
  CompleteOrderedRealField R ->
  (Nat -> R) ->
  Nat ->
  R
sumFromOneThrough reals term zero =
  zeroR reals
sumFromOneThrough reals term (suc n) =
  add reals
    (sumFromOneThrough reals term n)
    (term (suc n))

naturalAbsoluteDifference : Nat -> Nat -> Nat
naturalAbsoluteDifference zero n =
  n
naturalAbsoluteDifference (suc m) zero =
  suc m
naturalAbsoluteDifference (suc m) (suc n) =
  naturalAbsoluteDifference m n

StrictlyDecreasingAbsolute :
  {R : Set} ->
  CompleteOrderedRealField R ->
  (Nat -> R) ->
  Set
StrictlyDecreasingAbsolute reals x =
  (m n : Nat) ->
  Positive m ->
  Positive n ->
  NatStrictLess m n ->
  StrictLess reals
    (absoluteValue reals (x n))
    (absoluteValue reals (x m))

module Putnam1982A6Statement
  {R : Set}
  (reals : CompleteOrderedRealField R) where

  displacementTerm :
    (Nat -> Nat) ->
    (Nat -> R) ->
    Nat ->
    R
  displacementTerm b x n =
    multiply reals
      (fromNat reals
        (naturalAbsoluteDifference (b n) n))
      (absoluteValue reals (x n))

  partialSums :
    (Nat -> R) ->
    Nat ->
    R
  partialSums x n =
    sumFromOneThrough reals x n

  rearrangedPartialSums :
    (Nat -> Nat) ->
    (Nat -> R) ->
    Nat ->
    R
  rearrangedPartialSums b x n =
    sumFromOneThrough reals
      (\ k -> x (b k))
      n

  RearrangementClaim : Set
  RearrangementClaim =
    (b : Nat -> Nat) ->
    (x : Nat -> R) ->
    PositiveBijection b ->
    StrictlyDecreasingAbsolute reals x ->
    ConvergesTo reals
      (displacementTerm b x)
      (zeroR reals) ->
    ConvergesTo reals
      (partialSums x)
      (oneR reals) ->
    ConvergesTo reals
      (rearrangedPartialSums b x)
      (oneR reals)

  solution : Set
  solution =
    Bottom

  proposition : Set
  proposition =
    Iff RearrangementClaim solution

putnam-1982-a6 : Set1
putnam-1982-a6 =
  (R : Set) ->
  (reals : CompleteOrderedRealField R) ->
  Putnam1982A6Statement.proposition reals
