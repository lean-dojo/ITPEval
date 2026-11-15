-- Statement-only formalization of PutnamBench corpus artifact putnam_1993_a4:
-- bounded positive integer sequences of lengths 19 and 93 have equal subset
-- sums with the subset of the first sequence nonempty. This file contains no proof.

{-# OPTIONS --safe #-}

module Putnam1993A4 where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality renaming (_≡_ to _==_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)

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

data Positive : Nat -> Set where
  positive : {n : Nat} -> Positive (suc n)

Subset : Nat -> Set
Subset n =
  Fin n -> Bool

Nonempty :
  {n : Nat} ->
  Subset n ->
  Set
Nonempty {n} subset =
  Exists (Fin n) (\ index -> subset index == true)

selectedSum :
  {n : Nat} ->
  (Fin n -> Nat) ->
  Subset n ->
  Nat
selectedSum {zero} values subset =
  zero
selectedSum {suc n} values subset with subset fzero
... | false =
  selectedSum
    (\ index -> values (fsuc index))
    (\ index -> subset (fsuc index))
... | true =
  values fzero +
  selectedSum
    (\ index -> values (fsuc index))
    (\ index -> subset (fsuc index))

BoundedPositive :
  {n : Nat} ->
  (Fin n -> Nat) ->
  Nat ->
  Set
BoundedPositive {n} values upper =
  (index : Fin n) ->
  Positive (values index)
  and
  values index <=N upper

putnam-1993-a4 : Set
putnam-1993-a4 =
  (x : Fin 19 -> Nat) ->
  (y : Fin 93 -> Nat) ->
  BoundedPositive x 93 ->
  BoundedPositive y 19 ->
  Exists (Subset 19)
    (\ is ->
      Exists (Subset 93)
        (\ js ->
          Nonempty is
          and
          selectedSum x is == selectedSum y js))
