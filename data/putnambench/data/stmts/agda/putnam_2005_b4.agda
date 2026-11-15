-- Statement-only formalization of PutnamBench corpus artifact putnam_2005_b4
-- (putnambench__agda__putnam_2005_b4): symmetry in the number of integer
-- tuples of fixed positive length whose sum of absolute values is bounded
-- by a positive integer. This file contains no proof.

{-# OPTIONS --safe #-}

module Putnam2005B4 where

open import Agda.Builtin.Equality renaming (_≡_ to _==_)
open import Agda.Builtin.Int using (Int; pos; negsuc)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)

infix 4 _<=N_
infixr 5 _::_

record Exists (A : Set) (P : A -> Set) : Set where
  constructor witness
  field
    value    : A
    property : P value

data _<=N_ : Nat -> Nat -> Set where
  zero<=N   : {n : Nat} -> zero <=N n
  suc<=sucN : {m n : Nat} -> m <=N n -> suc m <=N suc n

data Fin : Nat -> Set where
  fzero : {n : Nat} -> Fin (suc n)
  fsuc  : {n : Nat} -> Fin n -> Fin (suc n)

data Vec (A : Set) : Nat -> Set where
  []   : Vec A zero
  _::_ : {n : Nat} -> A -> Vec A n -> Vec A (suc n)

record HasCardinality
  {A : Set}
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
        (\ index -> item == enumerate index)

    enumeration-injective :
      (left-index right-index : Fin cardinality) ->
      enumerate left-index == enumerate right-index ->
      left-index == right-index

one : Nat
one =
  suc zero

Positive : Nat -> Set
Positive n =
  one <=N n

absoluteValue : Int -> Nat
absoluteValue (pos n) =
  n
absoluteValue (negsuc n) =
  suc n

sumAbsoluteValues :
  {n : Nat} ->
  Vec Int n ->
  Nat
sumAbsoluteValues [] =
  zero
sumAbsoluteValues (x :: xs) =
  absoluteValue x + sumAbsoluteValues xs

BoundedTuple :
  {n : Nat} ->
  Nat ->
  Vec Int n ->
  Set
BoundedTuple bound tuple =
  sumAbsoluteValues tuple <=N bound

CountsBoundedTuples :
  (Nat -> Nat -> Nat) ->
  Set
CountsBoundedTuples f =
  (m n : Nat) ->
  Positive m ->
  Positive n ->
  HasCardinality
    (BoundedTuple {n = n} m)
    (f m n)

putnam-2005-b4 : Set
putnam-2005-b4 =
  (m n : Nat) ->
  Positive m ->
  Positive n ->
  (f : Nat -> Nat -> Nat) ->
  CountsBoundedTuples f ->
  f m n == f n m
