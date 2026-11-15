-- Statement-only formalization of PutnamBench corpus artifact putnam_1962_b5:
-- for every integer n greater than one, the sum from i = 1 through n of
-- (i / n) raised to n lies between (3n + 1) / (2n + 2) and 2.
-- This file contains no proof.

{-# OPTIONS --safe #-}

module Putnam1962B5 where

open import Agda.Builtin.Equality renaming (_≡_ to _==_)
open import Agda.Builtin.Int using (Int; pos; negsuc)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)

infix 4 _!=_
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
    fromNat-addition :
      (m n : Nat) ->
      fromNat (m + n) == add (fromNat m) (fromNat n)
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
          (x : R) ->
          P x ->
          lessOrEqual x upper) ->
      Exists R
        (\ supremum ->
          ((x : R) -> P x -> lessOrEqual x supremum)
          and
          ((upper : R) ->
            ((x : R) -> P x -> lessOrEqual x upper) ->
            lessOrEqual supremum upper))

open CompleteOrderedField

data IntegerGreaterThanOne : Int -> Set where
  positive-at-least-two :
    (k : Nat) ->
    IntegerGreaterThanOne (pos (suc (suc k)))

integerNaturalPart : Int -> Nat
integerNaturalPart (pos n) = n
integerNaturalPart (negsuc n) = zero

divide :
  {R : Set} ->
  CompleteOrderedField R ->
  R ->
  R ->
  R
divide reals x y =
  multiply reals x (inverse reals y)

naturalPower :
  {R : Set} ->
  CompleteOrderedField R ->
  R ->
  Nat ->
  R
naturalPower reals x zero =
  oneR reals
naturalPower reals x (suc n) =
  multiply reals
    (naturalPower reals x n)
    x

sumFromOne :
  {R : Set} ->
  CompleteOrderedField R ->
  Nat ->
  (Nat -> R) ->
  R
sumFromOne reals zero term =
  zeroR reals
sumFromOne reals (suc n) term =
  add reals
    (sumFromOne reals n term)
    (term (suc n))

StrictLess :
  {R : Set} ->
  CompleteOrderedField R ->
  R ->
  R ->
  Set
StrictLess reals x y =
  lessOrEqual reals x y and x != y

two :
  {R : Set} ->
  CompleteOrderedField R ->
  R
two reals =
  fromNat reals (suc (suc zero))

three :
  {R : Set} ->
  CompleteOrderedField R ->
  R
three reals =
  fromNat reals (suc (suc (suc zero)))

putnamSum :
  {R : Set} ->
  CompleteOrderedField R ->
  Int ->
  R
putnamSum reals n =
  sumFromOne reals (integerNaturalPart n)
    (\ i ->
      naturalPower reals
        (divide reals
          (fromNat reals i)
          (fromNat reals (integerNaturalPart n)))
        (integerNaturalPart n))

lowerBound :
  {R : Set} ->
  CompleteOrderedField R ->
  Int ->
  R
lowerBound reals n =
  divide reals
    (add reals
      (multiply reals
        (three reals)
        (fromNat reals (integerNaturalPart n)))
      (oneR reals))
    (add reals
      (multiply reals
        (two reals)
        (fromNat reals (integerNaturalPart n)))
      (two reals))

module Putnam1962B5Statement
  {R : Set}
  (reals : CompleteOrderedField R) where

  proposition : Set
  proposition =
    (n : Int) ->
    IntegerGreaterThanOne n ->
    StrictLess reals
      (lowerBound reals n)
      (putnamSum reals n)
    and
    StrictLess reals
      (putnamSum reals n)
      (two reals)

putnam-1962-b5 : Set1
putnam-1962-b5 =
  (R : Set) ->
  (reals : CompleteOrderedField R) ->
  Putnam1962B5Statement.proposition reals
