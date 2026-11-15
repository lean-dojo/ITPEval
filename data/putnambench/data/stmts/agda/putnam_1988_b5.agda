-- Statement-only formalization of PutnamBench corpus artifact putnam_1988_b5:
-- the prescribed skew-symmetric real matrix of odd size 2n+1 has rank 2n.
-- This file contains no proof.

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

record Exists (A : Set) (P : A -> Set) : Set where
  constructor witness
  field
    value    : A
    property : P value

data _<=N_ : Nat -> Nat -> Set where
  zero<=N   : {n : Nat} -> zero <=N n
  suc<=sucN : {m n : Nat} -> m <=N n -> suc m <=N suc n

data Fin : Nat -> Set where
  fzero : {n : Nat} -> Fin (suc n)
  fsuc  : {n : Nat} -> Fin n -> Fin (suc n)

toNat : {n : Nat} -> Fin n -> Nat
toNat fzero =
  zero
toNat (fsuc i) =
  suc (toNat i)

subtractNat : Nat -> Nat -> Nat
subtractNat m zero =
  m
subtractNat zero (suc n) =
  zero
subtractNat (suc m) (suc n) =
  subtractNat m n

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

Matrix : Set -> Nat -> Nat -> Set
Matrix R rows columns =
  Fin rows -> Fin columns -> R

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
  Matrix R (suc n) (suc n) ->
  Fin (suc n) ->
  Matrix R n n
firstRowMinor A removedColumn i j =
  A (fsuc i) (skip removedColumn j)

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
  Matrix R n n ->
  R
determinant reals {zero} A =
  oneR reals
determinant reals {suc n} A =
  sumFin reals
    (\ column ->
      multiply reals
        (alternatingSign reals column)
        (multiply reals
          (A fzero column)
          (determinant reals (firstRowMinor A column))))

Injective :
  {A B : Set} ->
  (A -> B) ->
  Set
Injective f =
  (x y : _) ->
  f x == f y ->
  x == y

submatrix :
  {R : Set} {rows columns k : Nat} ->
  Matrix R rows columns ->
  (Fin k -> Fin rows) ->
  (Fin k -> Fin columns) ->
  Matrix R k k
submatrix A selectedRows selectedColumns i j =
  A (selectedRows i) (selectedColumns j)

RankAtLeast :
  {R : Set} {rows columns : Nat} ->
  CompleteOrderedRealField R ->
  Matrix R rows columns ->
  Nat ->
  Set
RankAtLeast {rows = rows} {columns = columns} reals A k =
  Exists (Fin k -> Fin rows)
    (\ selectedRows ->
      Injective selectedRows
      and
      Exists (Fin k -> Fin columns)
        (\ selectedColumns ->
          Injective selectedColumns
          and
          determinant reals
            (submatrix A selectedRows selectedColumns)
          !=
          zeroR reals))

HasRank :
  {R : Set} {rows columns : Nat} ->
  CompleteOrderedRealField R ->
  Matrix R rows columns ->
  Nat ->
  Set
HasRank reals A k =
  RankAtLeast reals A k
  and
  Not (RankAtLeast reals A (suc k))

twoN : Nat
twoN =
  suc (suc zero)

matrixSize : Nat -> Nat
matrixSize n =
  suc (twoN * n)

rankValue : Nat -> Nat
rankValue n =
  twoN * n

PositiveNat : Nat -> Set
PositiveNat n =
  suc zero <=N n

SkewSymmetric :
  {R : Set} ->
  CompleteOrderedRealField R ->
  {n : Nat} ->
  Matrix R n n ->
  Set
SkewSymmetric reals A =
  (i j : _) ->
  A i j == negate reals (A j i)

FirstSubdiagonalsAreOne :
  {R : Set} ->
  CompleteOrderedRealField R ->
  (n : Nat) ->
  Matrix R (matrixSize n) (matrixSize n) ->
  Set
FirstSubdiagonalsAreOne reals n A =
  (i j : Fin (matrixSize n)) ->
  (suc (toNat j) <=N toNat i)
  and
  (subtractNat (toNat i) (toNat j) <=N n) ->
  A i j == oneR reals

RemainingLowerEntriesAreNegativeOne :
  {R : Set} ->
  CompleteOrderedRealField R ->
  (n : Nat) ->
  Matrix R (matrixSize n) (matrixSize n) ->
  Set
RemainingLowerEntriesAreNegativeOne reals n A =
  (i j : Fin (matrixSize n)) ->
  suc n <=N subtractNat (toNat i) (toNat j) ->
  A i j == negate reals (oneR reals)

putnam-1988-b5 : Set1
putnam-1988-b5 =
  (R : Set) ->
  (reals : CompleteOrderedRealField R) ->
  (n : Nat) ->
  PositiveNat n ->
  (Mn : Matrix R (matrixSize n) (matrixSize n)) ->
  SkewSymmetric reals Mn ->
  FirstSubdiagonalsAreOne reals n Mn ->
  RemainingLowerEntriesAreNegativeOne reals n Mn ->
  HasRank reals Mn (rankValue n)
