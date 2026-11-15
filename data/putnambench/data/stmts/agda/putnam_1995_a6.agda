-- Statement-only formalization of PutnamBench corpus artifact putnam_1995_a6
-- (putnambench__agda__putnam_1995_a6): a cardinality comparison for matrices
-- whose columns are permutations of 1, 2, 3 and whose row sums are consecutive
-- or equal. This file contains no proof.

{-# OPTIONS --safe #-}

open import Agda.Builtin.Equality renaming (_≡_ to _==_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)

infix 4 _<=N_
infixr 3 _and_

record _and_ (A B : Set) : Set where
  constructor both
  field
    first  : A
    second : B

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

one two three four : Nat
one =
  suc zero
two =
  suc one
three =
  suc two
four =
  suc three

row0 row1 row2 : Fin three
row0 =
  fzero
row1 =
  fsuc fzero
row2 =
  fsuc (fsuc fzero)

data ColumnOrder : Set where
  order123 order132 order213 order231 order312 order321 : ColumnOrder

columnValue :
  ColumnOrder ->
  Fin three ->
  Nat
columnValue order123 fzero =
  one
columnValue order123 (fsuc fzero) =
  two
columnValue order123 (fsuc (fsuc fzero)) =
  three
columnValue order132 fzero =
  one
columnValue order132 (fsuc fzero) =
  three
columnValue order132 (fsuc (fsuc fzero)) =
  two
columnValue order213 fzero =
  two
columnValue order213 (fsuc fzero) =
  one
columnValue order213 (fsuc (fsuc fzero)) =
  three
columnValue order231 fzero =
  two
columnValue order231 (fsuc fzero) =
  three
columnValue order231 (fsuc (fsuc fzero)) =
  one
columnValue order312 fzero =
  three
columnValue order312 (fsuc fzero) =
  one
columnValue order312 (fsuc (fsuc fzero)) =
  two
columnValue order321 fzero =
  three
columnValue order321 (fsuc fzero) =
  two
columnValue order321 (fsuc (fsuc fzero)) =
  one

Matrix : Nat -> Set
Matrix n =
  Fin n -> ColumnOrder

sumFinNat :
  {n : Nat} ->
  (Fin n -> Nat) ->
  Nat
sumFinNat {zero} terms =
  zero
sumFinNat {suc n} terms =
  terms fzero +
  sumFinNat (\ index -> terms (fsuc index))

rowSum :
  {n : Nat} ->
  Matrix n ->
  Fin three ->
  Nat
rowSum matrix row =
  sumFinNat
    (\ column ->
      columnValue (matrix column) row)

consecutiveValue :
  ColumnOrder ->
  Fin three ->
  Nat ->
  Nat
consecutiveValue order123 fzero start =
  start
consecutiveValue order123 (fsuc fzero) start =
  suc start
consecutiveValue order123 (fsuc (fsuc fzero)) start =
  suc (suc start)
consecutiveValue order132 fzero start =
  start
consecutiveValue order132 (fsuc fzero) start =
  suc (suc start)
consecutiveValue order132 (fsuc (fsuc fzero)) start =
  suc start
consecutiveValue order213 fzero start =
  suc start
consecutiveValue order213 (fsuc fzero) start =
  start
consecutiveValue order213 (fsuc (fsuc fzero)) start =
  suc (suc start)
consecutiveValue order231 fzero start =
  suc start
consecutiveValue order231 (fsuc fzero) start =
  suc (suc start)
consecutiveValue order231 (fsuc (fsuc fzero)) start =
  start
consecutiveValue order312 fzero start =
  suc (suc start)
consecutiveValue order312 (fsuc fzero) start =
  start
consecutiveValue order312 (fsuc (fsuc fzero)) start =
  suc start
consecutiveValue order321 fzero start =
  suc (suc start)
consecutiveValue order321 (fsuc fzero) start =
  suc start
consecutiveValue order321 (fsuc (fsuc fzero)) start =
  start

RowsAreConsecutive :
  {n : Nat} ->
  Matrix n ->
  Set
RowsAreConsecutive matrix =
  Exists Nat
    (\ start ->
      Exists ColumnOrder
        (\ ordering ->
          (row : Fin three) ->
          rowSum matrix row ==
          consecutiveValue ordering row start))

RowsAreEqual :
  {n : Nat} ->
  Matrix n ->
  Set
RowsAreEqual matrix =
  rowSum matrix row0 == rowSum matrix row1
  and
  rowSum matrix row1 == rowSum matrix row2

record ConsecutiveMatrix (n : Nat) : Set where
  constructor consecutiveMatrix
  field
    matrix      : Matrix n
    consecutive : RowsAreConsecutive matrix

record EqualSumMatrix (n : Nat) : Set where
  constructor equalSumMatrix
  field
    matrix : Matrix n
    equal  : RowsAreEqual matrix

SameConsecutiveMatrix :
  {n : Nat} ->
  ConsecutiveMatrix n ->
  ConsecutiveMatrix n ->
  Set
SameConsecutiveMatrix {n} left right =
  (column : Fin n) ->
  ConsecutiveMatrix.matrix left column ==
  ConsecutiveMatrix.matrix right column

SameEqualSumMatrix :
  {n : Nat} ->
  EqualSumMatrix n ->
  EqualSumMatrix n ->
  Set
SameEqualSumMatrix {n} left right =
  (column : Fin n) ->
  EqualSumMatrix.matrix left column ==
  EqualSumMatrix.matrix right column

record HasExtensionalCardinality
  {A : Set}
  (equivalent : A -> A -> Set)
  (cardinality : Nat) :
  Set where

  field
    enumerate :
      Fin cardinality ->
      A

    enumeration-complete :
      (item : A) ->
      Exists (Fin cardinality)
        (\ index ->
          equivalent item (enumerate index))

    enumeration-injective :
      (left-index right-index : Fin cardinality) ->
      equivalent (enumerate left-index) (enumerate right-index) ->
      left-index == right-index

ConsecutiveFamilyHasCardinality :
  Nat ->
  Nat ->
  Set
ConsecutiveFamilyHasCardinality n cardinality =
  HasExtensionalCardinality
    {A = ConsecutiveMatrix n}
    SameConsecutiveMatrix
    cardinality

EqualSumFamilyHasCardinality :
  Nat ->
  Nat ->
  Set
EqualSumFamilyHasCardinality n cardinality =
  HasExtensionalCardinality
    {A = EqualSumMatrix n}
    SameEqualSumMatrix
    cardinality

putnam-1995-a6 : Set
putnam-1995-a6 =
  Exists Nat
    (\ n ->
      1995 <=N n
      and
      Exists Nat
        (\ consecutive-count ->
          ConsecutiveFamilyHasCardinality n consecutive-count
          and
          Exists Nat
            (\ equal-count ->
              EqualSumFamilyHasCardinality n equal-count
              and
              four * equal-count <=N consecutive-count)))
