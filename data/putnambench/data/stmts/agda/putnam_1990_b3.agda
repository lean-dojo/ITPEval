-- Statement-only formalization of PutnamBench corpus artifact putnam_1990_b3:
-- a sufficiently large set of 2 by 2 natural-number matrices with square
-- entries at most 200 contains two distinct commuting matrices. This file contains no proof.

{-# OPTIONS --safe #-}

open import Agda.Builtin.Equality renaming (_≡_ to _==_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)

infix 4 _!=_ _<=N_ _<N_
infixr 3 _and_

data Bottom : Set where

Not : Set -> Set
Not proposition =
  proposition -> Bottom

_!=_ : {A : Set} -> A -> A -> Set
x != y =
  Not (x == y)

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

_<N_ : Nat -> Nat -> Set
m <N n =
  suc m <=N n

data Fin : Nat -> Set where
  fzero : {n : Nat} -> Fin (suc n)
  fsuc  : {n : Nat} -> Fin n -> Fin (suc n)

record Matrix2 : Set where
  constructor matrix
  field
    entry00 : Nat
    entry01 : Nat
    entry10 : Nat
    entry11 : Nat

open Matrix2

MatrixEqual : Matrix2 -> Matrix2 -> Set
MatrixEqual A B =
  entry00 A == entry00 B
  and
  entry01 A == entry01 B
  and
  entry10 A == entry10 B
  and
  entry11 A == entry11 B

MatrixDistinct : Matrix2 -> Matrix2 -> Set
MatrixDistinct A B =
  Not (MatrixEqual A B)

matrixMultiply : Matrix2 -> Matrix2 -> Matrix2
matrixMultiply A B =
  matrix
    (entry00 A * entry00 B + entry01 A * entry10 B)
    (entry00 A * entry01 B + entry01 A * entry11 B)
    (entry10 A * entry00 B + entry11 A * entry10 B)
    (entry10 A * entry01 B + entry11 A * entry11 B)

SquareAtMost : Nat -> Set
SquareAtMost n =
  Exists Nat (\ root -> n == root * root)
  and
  n <=N 200

AdmissibleMatrix : Matrix2 -> Set
AdmissibleMatrix A =
  SquareAtMost (entry00 A)
  and
  SquareAtMost (entry01 A)
  and
  SquareAtMost (entry10 A)
  and
  SquareAtMost (entry11 A)

record HasMoreThan
  (member : Matrix2 -> Set)
  (lowerBound : Nat) :
  Set where

  field
    enumerate :
      Fin (suc lowerBound) ->
      Matrix2
    enumerated-member :
      (index : Fin (suc lowerBound)) ->
      member (enumerate index)
    enumeration-injective :
      (left-index right-index : Fin (suc lowerBound)) ->
      MatrixEqual (enumerate left-index) (enumerate right-index) ->
      left-index == right-index

CommutingDistinctMembers :
  (Matrix2 -> Set) ->
  Set
CommutingDistinctMembers member =
  Exists Matrix2
    (\ A ->
      member A
      and
      Exists Matrix2
        (\ B ->
          member B
          and
          MatrixDistinct A B
          and
          MatrixEqual
            (matrixMultiply A B)
            (matrixMultiply B A)))

putnam-1990-b3 : Set1
putnam-1990-b3 =
  (S : Matrix2 -> Set) ->
  ((A : Matrix2) ->
    S A ->
    AdmissibleMatrix A) ->
  HasMoreThan S 50387 ->
  CommutingDistinctMembers S
