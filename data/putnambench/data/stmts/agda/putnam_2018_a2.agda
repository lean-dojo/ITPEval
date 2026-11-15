-- Statement-only formalization of PutnamBench corpus artifact putnam_2018_a2
-- (putnambench__agda__putnam_2018_a2): the determinant of the intersection
-- matrix of all nonempty subsets of an n-element set. This file contains no proof.

{-# OPTIONS --safe #-}

module Putnam2018A2 where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality renaming (_≡_ to _==_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _-_; _*_)

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

data Positive : Nat -> Set where
  positive : {n : Nat} -> Positive (suc n)

data Fin : Nat -> Set where
  fzero : {n : Nat} -> Fin (suc n)
  fsuc  : {n : Nat} -> Fin n -> Fin (suc n)

one : Nat
one =
  suc zero

two : Nat
two =
  suc one

naturalPowerNat : Nat -> Nat -> Nat
naturalPowerNat base zero =
  one
naturalPowerNat base (suc exponent) =
  naturalPowerNat base exponent * base

matrixSize : Nat -> Nat
matrixSize n =
  naturalPowerNat two n - one

boolAnd : Bool -> Bool -> Bool
boolAnd false other =
  false
boolAnd true other =
  other

boolOr : Bool -> Bool -> Bool
boolOr false other =
  other
boolOr true other =
  true

Subset : Nat -> Set
Subset n =
  Fin n -> Bool

SubsetEqual :
  {n : Nat} ->
  Subset n ->
  Subset n ->
  Set
SubsetEqual {n} firstSubset secondSubset =
  (i : Fin n) ->
  firstSubset i == secondSubset i

Nonempty :
  {n : Nat} ->
  Subset n ->
  Set
Nonempty {n} subset =
  Exists (Fin n)
    (\ i -> subset i == true)

intersects :
  {n : Nat} ->
  Subset n ->
  Subset n ->
  Bool
intersects {zero} firstSubset secondSubset =
  false
intersects {suc n} firstSubset secondSubset =
  boolOr
    (boolAnd (firstSubset fzero) (secondSubset fzero))
    (intersects
      (\ i -> firstSubset (fsuc i))
      (\ i -> secondSubset (fsuc i)))

record EnumeratesNonemptySubsets
  {n cardinality : Nat}
  (subsets : Fin cardinality -> Subset n) :
  Set where

  field
    enumeration-sound :
      (i : Fin cardinality) ->
      Nonempty (subsets i)

    enumeration-complete :
      (subset : Subset n) ->
      Nonempty subset ->
      Exists (Fin cardinality)
        (\ i -> SubsetEqual subset (subsets i))

    enumeration-injective :
      (i j : Fin cardinality) ->
      SubsetEqual (subsets i) (subsets j) ->
      i == j

Matrix : Set -> Nat -> Set
Matrix R n =
  Fin n -> Fin n -> R

sumFin :
  {R : Set} ->
  CompleteOrderedRealField R ->
  {n : Nat} ->
  (Fin n -> R) ->
  R
sumFin reals {zero} term =
  zeroR reals
sumFin reals {suc n} term =
  add reals
    (term fzero)
    (sumFin reals (\ i -> term (fsuc i)))

skip :
  {n : Nat} ->
  Fin (suc n) ->
  Fin n ->
  Fin (suc n)
skip {zero} removed ()
skip {suc n} fzero i =
  fsuc i
skip {suc n} (fsuc removed) fzero =
  fzero
skip {suc n} (fsuc removed) (fsuc i) =
  fsuc (skip removed i)

firstRowMinor :
  {R : Set} {n : Nat} ->
  Matrix R (suc n) ->
  Fin (suc n) ->
  Matrix R n
firstRowMinor matrix removedColumn i j =
  matrix (fsuc i) (skip removedColumn j)

alternatingSign :
  {R : Set} ->
  CompleteOrderedRealField R ->
  {n : Nat} ->
  Fin n ->
  R
alternatingSign reals fzero =
  oneR reals
alternatingSign reals (fsuc i) =
  negate reals (alternatingSign reals i)

determinant :
  {R : Set} ->
  CompleteOrderedRealField R ->
  {n : Nat} ->
  Matrix R n ->
  R
determinant reals {zero} matrix =
  oneR reals
determinant reals {suc n} matrix =
  sumFin reals
    (\ column ->
      multiply reals
        (alternatingSign reals column)
        (multiply reals
          (matrix fzero column)
          (determinant reals (firstRowMinor matrix column))))

entryValue :
  {R : Set} ->
  CompleteOrderedRealField R ->
  Bool ->
  R
entryValue reals false =
  zeroR reals
entryValue reals true =
  oneR reals

MatrixHasIntersectionEntries :
  {R : Set} ->
  (reals : CompleteOrderedRealField R) ->
  {n : Nat} ->
  (subsets : Fin (matrixSize n) -> Subset n) ->
  Matrix R (matrixSize n) ->
  Set
MatrixHasIntersectionEntries reals {n = n} subsets matrix =
  (i j : Fin (matrixSize n)) ->
  matrix i j ==
  entryValue reals (intersects (subsets i) (subsets j))

solution :
  {R : Set} ->
  CompleteOrderedRealField R ->
  Nat ->
  R
solution reals zero =
  negate reals (oneR reals)
solution reals (suc zero) =
  oneR reals
solution reals (suc (suc n)) =
  negate reals (oneR reals)

putnam-2018-a2 : Set1
putnam-2018-a2 =
  (R : Set) ->
  (reals : CompleteOrderedRealField R) ->
  (n : Nat) ->
  Positive n ->
  (subsets : Fin (matrixSize n) -> Subset n) ->
  EnumeratesNonemptySubsets subsets ->
  (matrix : Matrix R (matrixSize n)) ->
  MatrixHasIntersectionEntries reals subsets matrix ->
  determinant reals matrix == solution reals n
