-- Statement-only formalization of PutnamBench corpus artifact putnam_1978_b6:
-- an upper bound for the square of a weighted double sum of real numbers in
-- the unit interval. This file contains no proof.

{-# OPTIONS --safe #-}

module Putnam1978B6 where

open import Agda.Builtin.Equality renaming (_≡_ to _==_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)

infix 4 _!=_
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

data Positive : Nat -> Set where
  positive : (n : Nat) -> Positive (suc n)

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

twoN : Nat
twoN =
  suc (suc zero)

divide :
  {R : Set} ->
  CompleteOrderedRealField R ->
  R ->
  R ->
  R
divide reals x y =
  multiply reals x (inverse reals y)

square :
  {R : Set} ->
  CompleteOrderedRealField R ->
  R ->
  R
square reals x =
  multiply reals x x

InClosedUnitInterval :
  {R : Set} ->
  CompleteOrderedRealField R ->
  R ->
  Set
InClosedUnitInterval reals x =
  lessOrEqual reals (zeroR reals) x
  and
  lessOrEqual reals x (oneR reals)

sumFromOne :
  {R : Set} ->
  CompleteOrderedRealField R ->
  Nat ->
  (Nat -> R) ->
  R
sumFromOne reals zero term =
  zeroR reals
sumFromOne reals (suc n) term =
  add reals
    (sumFromOne reals n term)
    (term (suc n))

module Putnam1978B6Statement
  {R : Set}
  (reals : CompleteOrderedRealField R) where

  weightedInnerSum :
    (Nat -> Nat -> R) ->
    Nat ->
    Nat ->
    R
  weightedInnerSum a m i =
    sumFromOne reals (m * i)
      (\ j ->
        divide reals
          (a i j)
          (fromNat reals i))

  weightedDoubleSum :
    (Nat -> Nat -> R) ->
    Nat ->
    Nat ->
    R
  weightedDoubleSum a m n =
    sumFromOne reals n
      (weightedInnerSum a m)

  plainInnerSum :
    (Nat -> Nat -> R) ->
    Nat ->
    Nat ->
    R
  plainInnerSum a m i =
    sumFromOne reals (m * i) (a i)

  plainDoubleSum :
    (Nat -> Nat -> R) ->
    Nat ->
    Nat ->
    R
  plainDoubleSum a m n =
    sumFromOne reals n
      (plainInnerSum a m)

  rightHandSide :
    (Nat -> Nat -> R) ->
    Nat ->
    Nat ->
    R
  rightHandSide a m n =
    multiply reals
      (multiply reals
        (fromNat reals twoN)
        (fromNat reals m))
      (plainDoubleSum a m n)

  proposition : Set
  proposition =
    (a : Nat -> Nat -> R) ->
    ((i j : Nat) ->
      InClosedUnitInterval reals (a i j)) ->
    (m n : Nat) ->
    (Positive m and Positive n) ->
    lessOrEqual reals
      (square reals (weightedDoubleSum a m n))
      (rightHandSide a m n)

putnam-1978-b6 : Set1
putnam-1978-b6 =
  (R : Set) ->
  (reals : CompleteOrderedRealField R) ->
  Putnam1978B6Statement.proposition reals
