-- Statement-only formalization of PutnamBench corpus artifact putnam_1990_a6:
-- exactly 17711 ordered pairs of subsets of {1,...,10} are admissible, where
-- every element of either subset exceeds the size of the other subset.
-- This file contains no proof.

{-# OPTIONS --safe #-}

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality renaming (_≡_ to _==_)
open import Agda.Builtin.Nat using (Nat; zero; suc)

infix 4 _<N_

record Exists (A : Set) (P : A -> Set) : Set where
  constructor witness
  field
    value    : A
    property : P value

data Fin : Nat -> Set where
  fzero : {n : Nat} -> Fin (suc n)
  fsuc  : {n : Nat} -> Fin n -> Fin (suc n)

data _<N_ : Nat -> Nat -> Set where
  zero<sucN : {n : Nat} -> zero <N suc n
  suc<sucN  : {m n : Nat} -> m <N n -> suc m <N suc n

one two three four five six seven eight nine ten : Nat
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
ten =
  suc nine

finToNat :
  {n : Nat} ->
  Fin n ->
  Nat
finToNat fzero =
  zero
finToNat (fsuc index) =
  suc (finToNat index)

elementValue :
  Fin ten ->
  Nat
elementValue index =
  suc (finToNat index)

Subset : Set
Subset =
  Fin ten -> Bool

countTrue :
  {n : Nat} ->
  (Fin n -> Bool) ->
  Nat
countTrue {zero} membership =
  zero
countTrue {suc n} membership with membership fzero
... | false =
  countTrue (\ index -> membership (fsuc index))
... | true =
  suc (countTrue (\ index -> membership (fsuc index)))

subsetCardinality :
  Subset ->
  Nat
subsetCardinality =
  countTrue

record OrderedPair : Set where
  constructor orderedPair
  field
    firstSubset  : Subset
    secondSubset : Subset

open OrderedPair

record Admissible (pair : OrderedPair) : Set where
  field
    first-elements-large :
      (index : Fin ten) ->
      firstSubset pair index == true ->
      subsetCardinality (secondSubset pair) <N elementValue index

    second-elements-large :
      (index : Fin ten) ->
      secondSubset pair index == true ->
      subsetCardinality (firstSubset pair) <N elementValue index

record AdmissibleOrderedPair : Set where
  constructor admissibleOrderedPair
  field
    pair          : OrderedPair
    admissibility : Admissible pair

open AdmissibleOrderedPair

record SameOrderedPair (left right : OrderedPair) : Set where
  field
    same-first-subset :
      (index : Fin ten) ->
      firstSubset left index == firstSubset right index

    same-second-subset :
      (index : Fin ten) ->
      secondSubset left index == secondSubset right index

SameAdmissibleOrderedPair :
  AdmissibleOrderedPair ->
  AdmissibleOrderedPair ->
  Set
SameAdmissibleOrderedPair left right =
  SameOrderedPair (pair left) (pair right)

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
      (left-index right-index : Fin cardinality) ->
      equivalent (enumerate left-index) (enumerate right-index) ->
      left-index == right-index

putnam-1990-a6-solution : Nat
putnam-1990-a6-solution =
  17711

putnam-1990-a6 : Set
putnam-1990-a6 =
  HasExtensionalCardinality
    SameAdmissibleOrderedPair
    putnam-1990-a6-solution
