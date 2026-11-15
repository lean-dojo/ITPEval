-- Statement-only formalization of PutnamBench corpus artifact putnam_2022_a6:
-- for positive n, the largest m admitting 2n increasing real points in
-- (-1,1) whose first m odd-power interval-length sums equal one is n.
-- This file contains no proof.

{-# OPTIONS --safe #-}

module Putnam2022A6 where

open import Agda.Builtin.Equality renaming (_≡_ to _==_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_; _-_)

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

record Exists (A : Set) (P : A -> Set) : Set where
  constructor witness
  field
    value    : A
    property : P value

data _<=N_ : Nat -> Nat -> Set where
  zero<=N   : {n : Nat} -> zero <=N n
  suc<=sucN : {m n : Nat} -> m <=N n -> suc m <=N suc n

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

oneN : Nat
oneN =
  suc zero

twoN : Nat
twoN =
  suc oneN

Positive : Nat -> Set
Positive n =
  oneN <=N n

InClosedNatInterval : Nat -> Nat -> Nat -> Set
InClosedNatInterval lower upper k =
  lower <=N k and k <=N upper

StrictLess :
  {R : Set} ->
  CompleteOrderedRealField R ->
  R ->
  R ->
  Set
StrictLess reals x y =
  lessOrEqual reals x y and x != y

subtract :
  {R : Set} ->
  CompleteOrderedRealField R ->
  R ->
  R ->
  R
subtract reals x y =
  add reals x (negate reals y)

realPower :
  {R : Set} ->
  CompleteOrderedRealField R ->
  R ->
  Nat ->
  R
realPower reals x zero =
  oneR reals
realPower reals x (suc exponent) =
  multiply reals
    (realPower reals x exponent)
    x

sumPositive :
  {R : Set} ->
  CompleteOrderedRealField R ->
  Nat ->
  (Nat -> R) ->
  R
sumPositive reals zero term =
  zeroR reals
sumPositive reals (suc n) term =
  add reals
    (sumPositive reals n term)
    (term (suc n))

IncreasingPoints :
  {R : Set} ->
  CompleteOrderedRealField R ->
  Nat ->
  (Nat -> R) ->
  Set
IncreasingPoints reals n x =
  StrictLess reals
    (negate reals (oneR reals))
    (x oneN)
  and
  ((i : Nat) ->
    InClosedNatInterval oneN (twoN * n - oneN) i ->
    StrictLess reals (x i) (x (suc i)))
  and
  StrictLess reals
    (x (twoN * n))
    (oneR reals)

MomentEquations :
  {R : Set} ->
  CompleteOrderedRealField R ->
  Nat ->
  Nat ->
  (Nat -> R) ->
  Set
MomentEquations reals n m x =
  (k : Nat) ->
  InClosedNatInterval oneN m k ->
  sumPositive reals n
    (\ i ->
      subtract reals
        (realPower reals
          (x (twoN * i))
          (twoN * k - oneN))
        (realPower reals
          (x (twoN * i - oneN))
          (twoN * k - oneN)))
  ==
  oneR reals

Admissible :
  {R : Set} ->
  CompleteOrderedRealField R ->
  Nat ->
  Nat ->
  Set
Admissible {R} reals n m =
  Exists (Nat -> R)
    (\ x ->
      IncreasingPoints reals n x
      and
      MomentEquations reals n m x)

record IsGreatest
  (property : Nat -> Set)
  (greatest : Nat) :
  Set where

  field
    attained :
      property greatest
    upper-bound :
      (m : Nat) ->
      property m ->
      m <=N greatest

putnam-2022-a6-solution : Nat -> Nat
putnam-2022-a6-solution n =
  n

putnam-2022-a6 : Set1
putnam-2022-a6 =
  (R : Set) ->
  (reals : CompleteOrderedRealField R) ->
  (n : Nat) ->
  Positive n ->
  IsGreatest
    (Admissible reals n)
    (putnam-2022-a6-solution n)
