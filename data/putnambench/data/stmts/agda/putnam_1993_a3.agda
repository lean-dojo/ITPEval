-- Statement-only formalization of PutnamBench corpus artifact putnam_1993_a3:
-- the number of intersection-preserving maps from the power set of an
-- n-element set to an m-element chain equals the sum of j^n for 1 <= j <= m.
-- This file contains no proof.

{-# OPTIONS --safe #-}

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality renaming (_≡_ to _==_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)

data Fin : Nat -> Set where
  fzero : {n : Nat} -> Fin (suc n)
  fsuc  : {n : Nat} -> Fin n -> Fin (suc n)

data FiniteSubset : Nat -> Set where
  emptySubset : FiniteSubset zero
  addBit      : {n : Nat} -> Bool -> FiniteSubset n -> FiniteSubset (suc n)

boolAnd : Bool -> Bool -> Bool
boolAnd false right = false
boolAnd true right = right

intersection :
  {n : Nat} ->
  FiniteSubset n ->
  FiniteSubset n ->
  FiniteSubset n
intersection emptySubset emptySubset =
  emptySubset
intersection (addBit left leftTail) (addBit right rightTail) =
  addBit
    (boolAnd left right)
    (intersection leftTail rightTail)

minFin :
  {n : Nat} ->
  Fin n ->
  Fin n ->
  Fin n
minFin fzero right =
  fzero
minFin (fsuc left) fzero =
  fzero
minFin (fsuc left) (fsuc right) =
  fsuc (minFin left right)

record MeetPreservingMap (n m : Nat) : Set where
  field
    function :
      FiniteSubset n ->
      Fin m

    preserves-intersection :
      (left right : FiniteSubset n) ->
      function (intersection left right) ==
      minFin (function left) (function right)

open MeetPreservingMap

SameMeetPreservingMap :
  {n m : Nat} ->
  MeetPreservingMap n m ->
  MeetPreservingMap n m ->
  Set
SameMeetPreservingMap {n} left right =
  (subset : FiniteSubset n) ->
  function left subset == function right subset

record Exists (A : Set) (P : A -> Set) : Set where
  field
    witness  : A
    property : P witness

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
        (\ index -> equivalent item (enumerate index))

    enumeration-injective :
      (leftIndex rightIndex : Fin cardinality) ->
      equivalent (enumerate leftIndex) (enumerate rightIndex) ->
      leftIndex == rightIndex

MeetPreservingFamilyHasCardinality :
  (n m cardinality : Nat) ->
  Set
MeetPreservingFamilyHasCardinality n m cardinality =
  HasExtensionalCardinality
    {A = MeetPreservingMap n m}
    SameMeetPreservingMap
    cardinality

one : Nat
one =
  suc zero

power : Nat -> Nat -> Nat
power base zero =
  one
power base (suc exponent) =
  power base exponent * base

sumPowersThrough : Nat -> Nat -> Nat
sumPowersThrough exponent zero =
  zero
sumPowersThrough exponent (suc bound) =
  sumPowersThrough exponent bound +
  power (suc bound) exponent

data Positive : Nat -> Set where
  positive : {n : Nat} -> Positive (suc n)

putnam-1993-a3 : Set
putnam-1993-a3 =
  (c : Nat -> Nat -> Nat) ->
  ((n m : Nat) ->
    Positive n ->
    Positive m ->
    MeetPreservingFamilyHasCardinality n m (c n m)) ->
  (n m : Nat) ->
  Positive n ->
  Positive m ->
  c n m == sumPowersThrough n m
