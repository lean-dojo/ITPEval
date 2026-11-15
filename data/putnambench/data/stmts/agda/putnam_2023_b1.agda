-- Statement-only formalization of PutnamBench corpus artifact putnam_2023_b1
-- (putnambench__agda__putnam_2023_b1): the number of extensionally distinct
-- coin configurations reachable by diagonal legal moves on an m-by-n grid is
-- the binomial coefficient (m+n-2 choose m-1). This file contains no proof.

{-# OPTIONS --safe #-}

module Putnam2023B1 where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality renaming (_≡_ to _==_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _-_)

infix 4 _<N_
infixr 3 _and_

record _and_ (A B : Set) : Set where
  constructor both
  field
    first  : A
    second : B

data Bottom : Set where

Not : Set -> Set
Not A =
  A -> Bottom

record Exists (A : Set) (P : A -> Set) : Set where
  constructor witness
  field
    value    : A
    property : P value

data _<N_ : Nat -> Nat -> Set where
  zero-less-successor :
    {n : Nat} ->
    zero <N suc n
  successor-less-successor :
    {m n : Nat} ->
    m <N n ->
    suc m <N suc n

data Fin : Nat -> Set where
  fzero : {n : Nat} -> Fin (suc n)
  fsuc  : {n : Nat} -> Fin n -> Fin (suc n)

one : Nat
one =
  suc zero

two : Nat
two =
  suc one

pred : Nat -> Nat
pred zero =
  zero
pred (suc n) =
  n

boolAnd : Bool -> Bool -> Bool
boolAnd false right =
  false
boolAnd true right =
  right

lessThanBool : Nat -> Nat -> Bool
lessThanBool zero zero =
  false
lessThanBool zero (suc n) =
  true
lessThanBool (suc m) zero =
  false
lessThanBool (suc m) (suc n) =
  lessThanBool m n

choose : Nat -> Nat -> Nat
choose zero zero =
  one
choose zero (suc k) =
  zero
choose (suc n) zero =
  one
choose (suc n) (suc k) =
  choose n k + choose n (suc k)

Configuration : Set
Configuration =
  Nat -> Nat -> Bool

SameConfiguration :
  Configuration ->
  Configuration ->
  Set
SameConfiguration left right =
  (i j : Nat) ->
  left i j == right i j

initialConfiguration :
  Nat ->
  Nat ->
  Configuration
initialConfiguration m n i j =
  boolAnd
    (lessThanBool i (pred m))
    (lessThanBool j (pred n))

DifferentSquare :
  Nat ->
  Nat ->
  Nat ->
  Nat ->
  Set
DifferentSquare i1 j1 i2 j2 =
  Not ((i1 == i2) and (j1 == j2))

record LegalMove
  (m n : Nat)
  (before after : Configuration) :
  Set where

  field
    row :
      Nat
    column :
      Nat
    row-in-range :
      row <N pred m
    column-in-range :
      column <N pred n

    before-source-occupied :
      before row column == true
    before-south-empty :
      before (suc row) column == false
    before-east-empty :
      before row (suc column) == false
    before-southeast-empty :
      before (suc row) (suc column) == false

    after-source-empty :
      after row column == false
    after-south-empty :
      after (suc row) column == false
    after-east-empty :
      after row (suc column) == false
    after-southeast-occupied :
      after (suc row) (suc column) == true

    unchanged-elsewhere :
      (i j : Nat) ->
      DifferentSquare i j row column ->
      DifferentSquare i j (suc row) column ->
      DifferentSquare i j row (suc column) ->
      DifferentSquare i j (suc row) (suc column) ->
      before i j == after i j

data Reachable
  (m n : Nat) :
  Configuration ->
  Set where

  initial-reachable :
    Reachable m n (initialConfiguration m n)

  move-reachable :
    {before after : Configuration} ->
    Reachable m n before ->
    LegalMove m n before after ->
    Reachable m n after

record HasExtensionalCardinality
  {A : Set}
  (equivalent : A -> A -> Set)
  (member : A -> Set)
  (cardinality : Nat) :
  Set where

  field
    enumerate :
      Fin cardinality ->
      A

    enumerated-member :
      (index : Fin cardinality) ->
      member (enumerate index)

    enumeration-complete :
      (item : A) ->
      member item ->
      Exists (Fin cardinality)
        (\ index -> equivalent item (enumerate index))

    enumeration-injective :
      (left-index right-index : Fin cardinality) ->
      equivalent (enumerate left-index) (enumerate right-index) ->
      left-index == right-index

putnam-2023-b1 : Set
putnam-2023-b1 =
  (m n : Nat) ->
  zero <N m ->
  zero <N n ->
  HasExtensionalCardinality
    SameConfiguration
    (Reachable m n)
    (choose ((m + n) - two) (m - one))
