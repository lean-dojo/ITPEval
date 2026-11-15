-- Statement-only formalization of PutnamBench corpus artifact putnam_1985_b3:
-- a positive-integer array in which every positive integer occurs at exactly
-- eight positive index pairs has some entry a(m,n) greater than m*n.
-- This file contains no proof.

{-# OPTIONS --safe #-}

open import Agda.Builtin.Equality renaming (_≡_ to _==_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _*_)

infix 4 _<=N_ _<N_
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

_<N_ : Nat -> Nat -> Set
m <N n =
  suc m <=N n

record Pair : Set where
  constructor pair
  field
    first-coordinate  : Nat
    second-coordinate : Nat

open Pair

data Fin : Nat -> Set where
  fzero : {n : Nat} -> Fin (suc n)
  fsuc  : {n : Nat} -> Fin n -> Fin (suc n)

eightN : Nat
eightN =
  8

record HasCardinality
  (S : Pair -> Set)
  (cardinality : Nat) :
  Set where

  field
    enumerate :
      Fin cardinality ->
      Pair
    enumerated-member :
      (index : Fin cardinality) ->
      S (enumerate index)
    enumeration-complete :
      (entry : Pair) ->
      S entry ->
      Exists (Fin cardinality)
        (\ index -> entry == enumerate index)
    enumeration-injective :
      (left-index right-index : Fin cardinality) ->
      enumerate left-index == enumerate right-index ->
      left-index == right-index

Fiber :
  (Nat -> Nat -> Nat) ->
  Nat ->
  Pair ->
  Set
Fiber a k entry =
  zero <N first-coordinate entry
  and
  zero <N second-coordinate entry
  and
  a (first-coordinate entry) (second-coordinate entry) == k

putnam-1985-b3 : Set
putnam-1985-b3 =
  (a : Nat -> Nat -> Nat) ->
  ((m n : Nat) ->
    zero <N a m n) ->
  ((k : Nat) ->
    zero <N k ->
    HasCardinality (Fiber a k) eightN) ->
  Exists Nat
    (\ m ->
      Exists Nat
        (\ n ->
          zero <N m
          and
          zero <N n
          and
          m * n <N a m n))
