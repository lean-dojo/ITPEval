-- Statement-only formalization of PutnamBench corpus artifact putnam_2007_a3
-- (putnambench__agda__putnam_2007_a3): the probability that no prefix sum
-- of a random ordering of 1 through 3k+1 is divisible by 3.
-- This file contains no proof.

{-# OPTIONS --safe #-}

module Putnam2007A3 where

open import Agda.Builtin.Equality renaming (_≡_ to _==_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)

infix 4 _<=N_ _divides_

data Bottom : Set where

Not : Set -> Set
Not A =
  A -> Bottom

record Exists (A : Set) (P : A -> Set) : Set where
  constructor witness
  field
    value    : A
    property : P value

data _<=N_ : Nat -> Nat -> Set where
  zero<=N   : {n : Nat} -> zero <=N n
  suc<=sucN : {m n : Nat} -> m <=N n -> suc m <=N suc n

oneN : Nat
oneN =
  suc zero

twoN : Nat
twoN =
  suc oneN

threeN : Nat
threeN =
  suc twoN

Positive : Nat -> Set
Positive n =
  oneN <=N n

data Fin : Nat -> Set where
  fzero : {n : Nat} -> Fin (suc n)
  fsuc  : {n : Nat} -> Fin n -> Fin (suc n)

toNat : {n : Nat} -> Fin n -> Nat
toNat fzero =
  zero
toNat (fsuc i) =
  suc (toNat i)

record Bijection (A B : Set) : Set where
  field
    to      : A -> B
    from    : B -> A
    from-to : (x : A) -> from (to x) == x
    to-from : (y : B) -> to (from y) == y

open Bijection

Permutation : Nat -> Set
Permutation n =
  Bijection (Fin n) (Fin n)

PermutationEqual :
  {n : Nat} ->
  Permutation n ->
  Permutation n ->
  Set
PermutationEqual left right =
  (i : _) ->
  to left i == to right i

valueAt :
  {n : Nat} ->
  Permutation n ->
  Fin n ->
  Nat
valueAt permutation position =
  suc (toNat (to permutation position))

prefixSum :
  {n : Nat} ->
  (Fin n -> Nat) ->
  Fin n ->
  Nat
prefixSum {suc n} values fzero =
  values fzero
prefixSum {suc n} values (fsuc last) =
  values fzero
  + prefixSum
      (\ position -> values (fsuc position))
      last

record _divides_ (divisor dividend : Nat) : Set where
  field
    quotient : Nat
    equation : divisor * quotient == dividend

record GoodPermutation (n : Nat) : Set where
  field
    permutation : Permutation n
    no-divisible-prefix :
      (last : Fin n) ->
      Not
        (threeN divides
          prefixSum
            (valueAt permutation)
            last)

open GoodPermutation

GoodPermutationEqual :
  {n : Nat} ->
  GoodPermutation n ->
  GoodPermutation n ->
  Set
GoodPermutationEqual left right =
  PermutationEqual
    (permutation left)
    (permutation right)

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

factorial : Nat -> Nat
factorial zero =
  oneN
factorial (suc n) =
  suc n * factorial n

numberOfEntries : Nat -> Nat
numberOfEntries k =
  threeN * k + oneN

probabilityNumerator : Nat -> Nat
probabilityNumerator k =
  factorial k * factorial (suc k)

probabilityDenominator : Nat -> Nat
probabilityDenominator k =
  numberOfEntries k * factorial (twoN * k)

putnam-2007-a3 : Set
putnam-2007-a3 =
  (k : Nat) ->
  Positive k ->
  (permutationCount goodPermutationCount : Nat) ->
  HasExtensionalCardinality
    (PermutationEqual {numberOfEntries k})
    permutationCount ->
  HasExtensionalCardinality
    (GoodPermutationEqual {numberOfEntries k})
    goodPermutationCount ->
  probabilityDenominator k * goodPermutationCount
  ==
  permutationCount * probabilityNumerator k
