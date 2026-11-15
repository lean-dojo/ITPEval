-- Statement-only formalization of PutnamBench corpus artifact putnam_2013_b5
-- (putnambench__agda__putnam_2013_b5): the number of endofunctions of
-- X = {1,...,n} whose every orbit eventually reaches a value at most k is
-- k * n^(n-1). This file contains no proof.

{-# OPTIONS --safe #-}

module Putnam2013B5 where

open import Agda.Builtin.Equality renaming (_≡_ to _==_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _-_; _*_)

infix 4 _<=N_

record Exists (A : Set) (P : A -> Set) : Set where
  constructor witness
  field
    value    : A
    property : P value

data _<=N_ : Nat -> Nat -> Set where
  zero<=N   : {n : Nat} -> zero <=N n
  suc<=sucN : {m n : Nat} -> m <=N n -> suc m <=N suc n

data Positive : Nat -> Set where
  positive : {n : Nat} -> Positive (suc n)

data Fin : Nat -> Set where
  fzero : {n : Nat} -> Fin (suc n)
  fsuc  : {n : Nat} -> Fin n -> Fin (suc n)

toNat : {n : Nat} -> Fin n -> Nat
toNat fzero =
  zero
toNat (fsuc index) =
  suc (toNat index)

PointwiseEqual :
  {n : Nat} ->
  (Fin n -> Fin n) ->
  (Fin n -> Fin n) ->
  Set
PointwiseEqual {n} left-function right-function =
  (x : Fin n) ->
  left-function x == right-function x

iterate :
  {A : Set} ->
  (A -> A) ->
  Nat ->
  A ->
  A
iterate function zero x =
  x
iterate function (suc count) x =
  function (iterate function count x)

EventuallyAtMost :
  {n : Nat} ->
  Fin n ->
  (Fin n -> Fin n) ->
  Set
EventuallyAtMost {n} k function =
  (x : Fin n) ->
  Exists Nat
    (\ j ->
      toNat (iterate function j x) <=N toNat k)

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

one : Nat
one =
  suc zero

naturalPower : Nat -> Nat -> Nat
naturalPower base zero =
  one
naturalPower base (suc exponent) =
  naturalPower base exponent * base

putnam-2013-b5 : Set
putnam-2013-b5 =
  (n : Nat) ->
  Positive n ->
  (k : Fin n) ->
  HasExtensionalCardinality
    {A = Fin n -> Fin n}
    PointwiseEqual
    (EventuallyAtMost k)
    (suc (toNat k) * naturalPower n (n - one))
