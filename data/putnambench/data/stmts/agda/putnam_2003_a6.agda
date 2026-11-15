-- Statement-only formalization of PutnamBench corpus artifact putnam_2003_a6
-- (putnambench__agda__putnam_2003_a6): existence of a partition of the
-- nonnegative integers whose two parts have equal ordered distinct-pair
-- representation counts for every sum. This file contains no proof.

{-# OPTIONS --safe #-}

module Putnam2003A6 where

open import Agda.Builtin.Equality renaming (_≡_ to _==_)
open import Agda.Builtin.Nat using (Nat; suc; _+_)

infix 4 _!=_
infixr 3 _and_
infixr 2 _or_

data Bottom : Set where

Not :
  Set ->
  Set
Not A =
  A -> Bottom

_!=_ :
  {A : Set} ->
  A ->
  A ->
  Set
x != y =
  Not (x == y)

record _and_
  (A B : Set) :
  Set where

  constructor both
  field
    first  : A
    second : B

data _or_
  (A B : Set) :
  Set where

  left  : A -> A or B
  right : B -> A or B

record Exists
  (A : Set)
  (P : A -> Set) :
  Set where

  constructor witness
  field
    value    : A
    property : P value

data Fin : Nat -> Set where
  fzero : {n : Nat} -> Fin (suc n)
  fsuc  : {n : Nat} -> Fin n -> Fin (suc n)

record Pair : Set where
  constructor pair
  field
    first-coordinate  : Nat
    second-coordinate : Nat

open Pair

Subset : Set1
Subset =
  Nat -> Set

record HasCardinality
  {A : Set}
  (P : A -> Set)
  (cardinality : Nat) :
  Set where

  field
    enumerate :
      Fin cardinality ->
      A
    enumerated-member :
      (i : Fin cardinality) ->
      P (enumerate i)
    enumeration-complete :
      (x : A) ->
      P x ->
      Exists (Fin cardinality)
        (\ i -> enumerate i == x)
    enumeration-injective :
      (i j : Fin cardinality) ->
      enumerate i == enumerate j ->
      i == j

Representation :
  Subset ->
  Nat ->
  Pair ->
  Set
Representation S n p =
  S (first-coordinate p)
  and
  S (second-coordinate p)
  and
  first-coordinate p != second-coordinate p
  and
  first-coordinate p + second-coordinate p == n

EqualRepresentationCount :
  Subset ->
  Subset ->
  Nat ->
  Set
EqualRepresentationCount A B n =
  Exists Nat
    (\ cardinality ->
      HasCardinality
        (Representation A n)
        cardinality
      and
      HasCardinality
        (Representation B n)
        cardinality)

record IsPartition
  (A B : Subset) :
  Set where

  field
    covers-all :
      (n : Nat) ->
      A n or B n
    disjoint :
      (n : Nat) ->
      A n ->
      B n ->
      Bottom

record Putnam2003A6Witness : Set1 where
  field
    A B :
      Subset
    partition :
      IsPartition A B
    equal-representation-counts :
      (n : Nat) ->
      EqualRepresentationCount A B n

putnam-2003-a6 : Set1
putnam-2003-a6 =
  Putnam2003A6Witness
