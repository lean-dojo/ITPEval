-- Statement-only formalization of PutnamBench corpus artifact putnam_2002_a3
-- (putnambench__agda__putnam_2002_a3): the number of nonempty subsets of
-- {1,...,n} with integer average differs from n by an even integer. This file
-- contains no proof.

{-# OPTIONS --safe #-}

module Putnam2002A3 where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality renaming (_≡_ to _==_)
open import Agda.Builtin.Int using (Int; negsuc; pos)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)

infix 4 _<=N_
infixr 3 _andB_

data Fin : Nat -> Set where
  fzero : {n : Nat} -> Fin (suc n)
  fsuc  : {n : Nat} -> Fin n -> Fin (suc n)

data _<=N_ : Nat -> Nat -> Set where
  zero<=N   : {n : Nat} -> zero <=N n
  suc<=sucN : {m n : Nat} -> m <=N n -> suc m <=N suc n

record Exists (A : Set) (P : A -> Set) : Set where
  constructor witness
  field
    value    : A
    property : P value

one : Nat
one =
  suc zero

two : Nat
two =
  suc one

_andB_ : Bool -> Bool -> Bool
true andB right =
  right
false andB right =
  false

natEqual : Nat -> Nat -> Bool
natEqual zero zero =
  true
natEqual zero (suc right) =
  false
natEqual (suc left) zero =
  false
natEqual (suc left) (suc right) =
  natEqual left right

Subset : Nat -> Set
Subset n =
  Fin n -> Bool

emptySubset : Subset zero
emptySubset ()

prepend :
  {n : Nat} ->
  Bool ->
  Subset n ->
  Subset (suc n)
prepend choice tail fzero =
  choice
prepend choice tail (fsuc index) =
  tail index

countWhere :
  {n : Nat} ->
  (Subset n -> Bool) ->
  Nat
countWhere {zero} predicate with predicate emptySubset
... | true =
  one
... | false =
  zero
countWhere {suc n} predicate =
  countWhere {n} (\ tail -> predicate (prepend false tail))
  +
  countWhere {n} (\ tail -> predicate (prepend true tail))

subsetCardinality :
  {n : Nat} ->
  Subset n ->
  Nat
subsetCardinality {zero} subset =
  zero
subsetCardinality {suc n} subset with subset fzero
... | true =
  suc (subsetCardinality (\ index -> subset (fsuc index)))
... | false =
  subsetCardinality (\ index -> subset (fsuc index))

subsetSumFrom :
  Nat ->
  {n : Nat} ->
  Subset n ->
  Nat
subsetSumFrom offset {zero} subset =
  zero
subsetSumFrom offset {suc n} subset with subset fzero
... | true =
  suc offset
  +
  subsetSumFrom
    (suc offset)
    (\ index -> subset (fsuc index))
... | false =
  subsetSumFrom
    (suc offset)
    (\ index -> subset (fsuc index))

subsetSum :
  {n : Nat} ->
  Subset n ->
  Nat
subsetSum =
  subsetSumFrom zero

searchQuotient :
  Nat ->
  Nat ->
  Nat ->
  Bool
searchQuotient divisor dividend zero =
  natEqual (divisor * zero) dividend
searchQuotient divisor dividend (suc quotient) with
  natEqual (divisor * suc quotient) dividend
... | true =
  true
... | false =
  searchQuotient divisor dividend quotient

hasNaturalQuotient :
  Nat ->
  Nat ->
  Bool
hasNaturalQuotient divisor dividend =
  searchQuotient divisor dividend dividend

nonzero : Nat -> Bool
nonzero zero =
  false
nonzero (suc n) =
  true

hasIntegralAverage :
  {n : Nat} ->
  Subset n ->
  Bool
hasIntegralAverage subset =
  nonzero (subsetCardinality subset)
  andB
  hasNaturalQuotient
    (subsetCardinality subset)
    (subsetSum subset)

qualifyingSubsetCount : Nat -> Nat
qualifyingSubsetCount n =
  countWhere {n} hasIntegralAverage

difference : Nat -> Nat -> Int
difference zero zero =
  pos zero
difference (suc left) zero =
  pos (suc left)
difference zero (suc right) =
  negsuc right
difference (suc left) (suc right) =
  difference left right

addInt : Int -> Int -> Int
addInt (pos left) (pos right) =
  pos (left + right)
addInt (pos left) (negsuc right) =
  difference left (suc right)
addInt (negsuc left) (pos right) =
  difference right (suc left)
addInt (negsuc left) (negsuc right) =
  negsuc (suc (left + right))

record Even (integer : Int) : Set where
  constructor even
  field
    half     : Int
    equation : addInt half half == integer

putnam-2002-a3 : Set
putnam-2002-a3 =
  (n : Nat) ->
  two <=N n ->
  Even (difference (qualifyingSubsetCount n) n)
