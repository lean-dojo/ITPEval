-- Statement-only formalization of PutnamBench corpus artifact putnam_2025_b4
-- (putnambench__agda__putnam_2025_b4): a finite matrix of natural numbers
-- satisfying the stated zero region and unit-step conditions obeys the given
-- bound relating its entry sum and number of nonzero entries. This file
-- contains no proof.

{-# OPTIONS --safe #-}

module Putnam2025B4 where

open import Agda.Builtin.Equality renaming (_≡_ to _==_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)

infix 4 _<=N_
infixr 2 _or_

data _or_ (A B : Set) : Set where
  left  : A -> A or B
  right : B -> A or B

data _<=N_ : Nat -> Nat -> Set where
  zero<=N   : {n : Nat} -> zero <=N n
  suc<=sucN : {m n : Nat} -> m <=N n -> suc m <=N suc n

data Fin : Nat -> Set where
  fzero : {n : Nat} -> Fin (suc n)
  fsuc  : {n : Nat} -> Fin n -> Fin (suc n)

finValue : {n : Nat} -> Fin n -> Nat
finValue fzero =
  zero
finValue (fsuc index) =
  suc (finValue index)

castSucc : {n : Nat} -> Fin n -> Fin (suc n)
castSucc fzero =
  fzero
castSucc (fsuc index) =
  fsuc (castSucc index)

one : Nat
one =
  suc zero

two : Nat
two =
  suc one

three : Nat
three =
  suc two

four : Nat
four =
  suc three

Matrix : Nat -> Set
Matrix n =
  Fin n -> Fin n -> Nat

sumFin :
  (n : Nat) ->
  (Fin n -> Nat) ->
  Nat
sumFin zero term =
  zero
sumFin (suc n) term =
  term fzero +
  sumFin n (\ index -> term (fsuc index))

matrixSum :
  {n : Nat} ->
  Matrix n ->
  Nat
matrixSum {n} A =
  sumFin n
    (\ i ->
      sumFin n
        (\ j -> A i j))

nonzeroIndicator : Nat -> Nat
nonzeroIndicator zero =
  zero
nonzeroIndicator (suc value) =
  one

nonzeroCount :
  {n : Nat} ->
  Matrix n ->
  Nat
nonzeroCount {n} A =
  sumFin n
    (\ i ->
      sumFin n
        (\ j -> nonzeroIndicator (A i j)))

putnam-2025-b4 : Set
putnam-2025-b4 =
  (m : Nat) ->
  (A : Matrix (suc (suc m))) ->
  ((i j : Fin (suc (suc m))) ->
    finValue i + finValue j <=N m ->
    A i j == zero) ->
  ((i : Fin (suc m)) (j : Fin (suc (suc m))) ->
    A (fsuc i) j == A (castSucc i) j
    or
    A (fsuc i) j == A (castSucc i) j + one) ->
  ((i : Fin (suc (suc m))) (j : Fin (suc m)) ->
    A i (fsuc j) == A i (castSucc j)
    or
    A i (fsuc j) == A i (castSucc j) + one) ->
  (S : Nat) ->
  S == matrixSum A ->
  (N : Nat) ->
  N == nonzeroCount A ->
  three * S <=N (m + four) * N
