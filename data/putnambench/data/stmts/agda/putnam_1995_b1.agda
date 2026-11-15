-- Statement-only formalization of PutnamBench corpus artifact putnam_1995_b1
-- (putnambench__agda__putnam_1995_b1): two partitions of {1,...,9} share a
-- distinct pair whose containing parts have equal sizes in both partitions.
-- This file contains no proof.

{-# OPTIONS --safe #-}

module Putnam1995B1 where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality renaming (_≡_ to _==_)
open import Agda.Builtin.Nat using (Nat; zero; suc)

infix 4 _!=_
infixr 3 _and_

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

record Exists (A : Set) (P : A -> Set) : Set where
  constructor witness
  field
    value    : A
    property : P value

data Fin : Nat -> Set where
  fzero : {n : Nat} -> Fin (suc n)
  fsuc  : {n : Nat} -> Fin n -> Fin (suc n)

one two three four five six seven eight nine : Nat
one =
  suc zero
two =
  suc one
three =
  suc two
four =
  suc three
five =
  suc four
six =
  suc five
seven =
  suc six
eight =
  suc seven
nine =
  suc eight

Index : Set
Index =
  Fin nine

record Partition : Set where
  field
    same-block :
      Index ->
      Index ->
      Bool

    block-reflexive :
      (x : Index) ->
      same-block x x == true

    block-symmetric :
      (x y : Index) ->
      same-block x y == same-block y x

    block-transitive :
      (x y z : Index) ->
      same-block x y == true ->
      same-block y z == true ->
      same-block x z == true

open Partition

countTrue :
  {n : Nat} ->
  (Fin n -> Bool) ->
  Nat
countTrue {zero} predicate =
  zero
countTrue {suc n} predicate with predicate fzero
... | false =
  countTrue (\ index -> predicate (fsuc index))
... | true =
  suc (countTrue (\ index -> predicate (fsuc index)))

partSize :
  Partition ->
  Index ->
  Nat
partSize partition x =
  countTrue (same-block partition x)

putnam-1995-b1 : Set
putnam-1995-b1 =
  (first-partition second-partition : Partition) ->
  Exists Index
    (\ x ->
      Exists Index
        (\ y ->
          x != y
          and
          partSize first-partition x ==
          partSize first-partition y
          and
          partSize second-partition x ==
          partSize second-partition y))
