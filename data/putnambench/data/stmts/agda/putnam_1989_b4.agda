-- Statement-only formalization of PutnamBench corpus artifact putnam_1989_b4:
-- a countably infinite set has an uncountable collection of nonempty subsets
-- whose pairwise intersections are finite. This file contains no proof.

{-# OPTIONS --safe #-}

module Putnam1989B4 where

open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)

data Bottom : Set where

Not : Set -> Set
Not A =
  A -> Bottom

Not1 : Set1 -> Set1
Not1 A =
  A -> Bottom

record Iff (A B : Set) : Set where
  constructor equivalence
  field
    forward  : A -> B
    backward : B -> A

record Iff1 (A B : Set1) : Set1 where
  constructor equivalence1
  field
    forward1  : A -> B
    backward1 : B -> A

record Truth1 : Set1 where
  constructor true1

Subset : Set -> Set1
Subset A =
  A -> Set

Family : Set1
Family =
  Subset Nat -> Set

ExtensionalEqual :
  {A : Set} ->
  Subset A ->
  Subset A ->
  Set
ExtensionalEqual {A} left right =
  (x : A) ->
  Iff (left x) (right x)

data Member {A : Set} (x : A) : List A -> Set where
  at-head :
    {xs : List A} ->
    Member x (x ∷ xs)
  in-tail :
    {y : A} ->
    {xs : List A} ->
    Member x xs ->
    Member x (y ∷ xs)

emptySubset : Subset Nat
emptySubset _ =
  Bottom

NonemptySubset : Subset Nat -> Set
NonemptySubset subset =
  Not (ExtensionalEqual subset emptySubset)

record ExistsNat (property : Nat -> Set) : Set where
  field
    witness : Nat
    holds   : property witness

record FiniteIntersection
  (left right : Subset Nat) :
  Set where

  field
    elements : List Nat
    complete :
      (x : Nat) ->
      left x ->
      right x ->
      Member x elements

record CountableFamily (collection : Family) : Set1 where
  field
    enumerate : Nat -> Subset Nat
    covered :
      (subset : Subset Nat) ->
      collection subset ->
      ExistsNat
        (\ n -> ExtensionalEqual subset (enumerate n))

record AlmostDisjointUncountableFamily : Set1 where
  field
    collection : Family
    uncountable :
      Not1 (CountableFamily collection)
    members-nonempty :
      (subset : Subset Nat) ->
      collection subset ->
      NonemptySubset subset
    pairwise-finite-intersections :
      (left right : Subset Nat) ->
      collection left ->
      collection right ->
      Not (ExtensionalEqual left right) ->
      FiniteIntersection left right

putnam-1989-b4 : Set1
putnam-1989-b4 =
  Iff1 AlmostDisjointUncountableFamily Truth1
