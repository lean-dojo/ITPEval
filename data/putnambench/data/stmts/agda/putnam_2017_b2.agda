-- Statement-only formalization of PutnamBench corpus artifact putnam_2017_b2:
-- the least positive starting integer whose sum of 2017 consecutive positive
-- integers has no other representation of length greater than one is 16.
-- This file contains no proof.

{-# OPTIONS --safe #-}

module Putnam2017B2 where

open import Agda.Builtin.Equality renaming (_≡_ to _==_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)

infix 4 _<=N_ _<N_
infixr 3 _and_

record _and_ (A B : Set) : Set where
  constructor both
  field
    first  : A
    second : B

data _<=N_ : Nat -> Nat -> Set where
  zero<=   : {n : Nat} -> zero <=N n
  suc<=suc : {m n : Nat} -> m <=N n -> suc m <=N suc n

data _<N_ : Nat -> Nat -> Set where
  zero<   : {n : Nat} -> zero <N suc n
  suc<suc : {m n : Nat} -> m <N n -> suc m <N suc n

consecutiveSum : Nat -> Nat -> Nat
consecutiveSum a zero =
  zero
consecutiveSum a (suc k) =
  consecutiveSum a k + (a + k)

ValidStartingValue : Nat -> Set
ValidStartingValue a =
  zero <N a
  and
  ((b k : Nat) ->
    zero <N b ->
    suc zero <N k ->
    consecutiveSum a 2017 == consecutiveSum b k ->
    k == 2017)

putnam-2017-b2 : Set
putnam-2017-b2 =
  ValidStartingValue 16
  and
  ((a : Nat) ->
    ValidStartingValue a ->
    16 <=N a)
