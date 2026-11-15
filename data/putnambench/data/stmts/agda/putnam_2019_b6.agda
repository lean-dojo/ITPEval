-- Statement-only formalization of PutnamBench corpus artifact putnam_2019_b6
-- (putnambench__agda__putnam_2019_b6): every positive-dimensional integer
-- lattice has an independent set that uniquely dominates its complement.
-- This file contains no proof.

{-# OPTIONS --safe #-}

module Main where

open import Agda.Builtin.Equality renaming (_≡_ to _==_)
open import Agda.Builtin.Int using (Int; pos; negsuc)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)

infix 4 _!=_ _<=N_
infixr 3 _and_
infix 1 _iff_

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

record _iff_ (A B : Set) : Set where
  constructor equivalence
  field
    forward  : A -> B
    backward : B -> A

record Exists (A : Set) (P : A -> Set) : Set where
  constructor witness
  field
    value    : A
    property : P value

record ExistsUniqueBy
  (A : Set)
  (equivalent : A -> A -> Set)
  (P : A -> Set) :
  Set where

  constructor uniqueWitness
  field
    value      : A
    property   : P value
    uniqueness :
      (other : A) ->
      P other ->
      equivalent other value

data _<=N_ : Nat -> Nat -> Set where
  zero<=N   : {n : Nat} -> zero <=N n
  suc<=sucN : {m n : Nat} -> m <=N n -> suc m <=N suc n

data Fin : Nat -> Set where
  fzero : {n : Nat} -> Fin (suc n)
  fsuc  : {n : Nat} -> Fin n -> Fin (suc n)

oneN : Nat
oneN =
  suc zero

Positive : Nat -> Set
Positive n =
  oneN <=N n

negative : Nat -> Int
negative zero =
  pos zero
negative (suc n) =
  negsuc n

negateInt : Int -> Int
negateInt (pos n) =
  negative n
negateInt (negsuc n) =
  pos (suc n)

differenceNat : Nat -> Nat -> Int
differenceNat zero zero =
  pos zero
differenceNat (suc m) zero =
  pos (suc m)
differenceNat zero (suc n) =
  negsuc n
differenceNat (suc m) (suc n) =
  differenceNat m n

addInt : Int -> Int -> Int
addInt (pos m) (pos n) =
  pos (m + n)
addInt (pos m) (negsuc n) =
  differenceNat m (suc n)
addInt (negsuc m) (pos n) =
  differenceNat n (suc m)
addInt (negsuc m) (negsuc n) =
  negsuc (suc (m + n))

subtractInt : Int -> Int -> Int
subtractInt x y =
  addInt x (negateInt y)

absoluteValue : Int -> Nat
absoluteValue (pos n) =
  n
absoluteValue (negsuc n) =
  suc n

Point : Nat -> Set
Point n =
  Fin n -> Int

PointEqual :
  {n : Nat} ->
  Point n ->
  Point n ->
  Set
PointEqual {n} p q =
  (i : Fin n) ->
  p i == q i

Neighbor :
  {n : Nat} ->
  Point n ->
  Point n ->
  Set
Neighbor {n} p q =
  Exists (Fin n)
    (\ i ->
      absoluteValue (subtractInt (p i) (q i)) == oneN
      and
      ((j : Fin n) ->
        j != i ->
        p j == q j))

record LatticeSubset (n : Nat) : Set1 where
  field
    contains :
      Point n ->
      Set
    respects-point-equality :
      (p q : Point n) ->
      PointEqual p q ->
      contains p iff contains q

open LatticeSubset

record PerfectIndependentDominatingSet (n : Nat) : Set1 where
  field
    subset :
      LatticeSubset n
    independent :
      (p : Point n) ->
      contains subset p ->
      (q : Point n) ->
      Neighbor p q ->
      Not (contains subset q)
    uniquely-dominates-complement :
      (p : Point n) ->
      Not (contains subset p) ->
      ExistsUniqueBy
        (Point n)
        PointEqual
        (\ q ->
          contains subset q
          and
          Neighbor p q)

putnam-2019-b6 : Set1
putnam-2019-b6 =
  (n : Nat) ->
  Positive n ->
  PerfectIndependentDominatingSet n
