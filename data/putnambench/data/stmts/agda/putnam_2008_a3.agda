-- Statement-only formalization of PutnamBench corpus artifact putnam_2008_a3
-- (putnambench__agda__putnam_2008_a3): termination and choice-independence
-- of the finite positive-integer gcd/lcm replacement process.
-- This file contains no proof.

{-# OPTIONS --safe #-}

module Putnam2008A3 where

open import Agda.Builtin.Equality renaming (_≡_ to _==_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _*_)

infix 4 _!=_ _<_ _divides_
infixr 3 _and_

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

record Exists (A : Set) (P : A -> Set) : Set where
  constructor witness
  field
    value    : A
    property : P value

data Positive : Nat -> Set where
  positive : {n : Nat} -> Positive (suc n)

data Fin : Nat -> Set where
  fzero : {n : Nat} -> Fin (suc n)
  fsuc  : {n : Nat} -> Fin n -> Fin (suc n)

data _<_ : {n : Nat} -> Fin n -> Fin n -> Set where
  fzero<fsuc :
    {n : Nat} ->
    {j : Fin n} ->
    fzero < fsuc j
  fsuc<fsuc :
    {n : Nat} ->
    {i j : Fin n} ->
    i < j ->
    fsuc i < fsuc j

record _divides_ (divisor dividend : Nat) : Set where
  constructor division
  field
    quotient : Nat
    equation : divisor * quotient == dividend

record IsGCD (x y d : Nat) : Set where
  constructor is-gcd
  field
    gcd-divides-left :
      d divides x
    gcd-divides-right :
      d divides y
    every-common-divisor-divides-gcd :
      (c : Nat) ->
      c divides x ->
      c divides y ->
      c divides d

record IsLCM (x y m : Nat) : Set where
  constructor is-lcm
  field
    left-divides-lcm :
      x divides m
    right-divides-lcm :
      y divides m
    lcm-divides-every-common-multiple :
      (c : Nat) ->
      x divides c ->
      y divides c ->
      m divides c

Continue :
  {n : Nat} ->
  (Fin n -> Nat) ->
  Set
Continue {n} sequence =
  Exists (Fin n)
    (\ j ->
      Exists (Fin n)
        (\ k ->
          (j < k)
          and
          Not (sequence j divides sequence k)))

Initial :
  {n : Nat} ->
  (Fin n -> Nat) ->
  (Nat -> Fin n -> Nat) ->
  Set
Initial {n} initial process =
  (i : Fin n) ->
  process zero i == initial i

Transition :
  {n : Nat} ->
  (Nat -> Fin n -> Nat) ->
  Set
Transition {n} process =
  (t : Nat) ->
  Continue (process t) ->
  Exists (Fin n)
    (\ j ->
      Exists (Fin n)
        (\ k ->
          (j < k)
          and
          (Not (process t j divides process t k)
          and
          (IsGCD
            (process t j)
            (process t k)
            (process (suc t) j)
          and
          (IsLCM
            (process t j)
            (process t k)
            (process (suc t) k)
          and
          ((i : Fin n) ->
            i != j ->
            i != k ->
            process (suc t) i == process t i))))))

putnam-2008-a3 : Set
putnam-2008-a3 =
  (n : Nat) ->
  Positive n ->
  (initial : Fin n -> Nat) ->
  ((i : Fin n) -> Positive (initial i)) ->
  Exists (Fin n -> Nat)
    (\ final ->
      (process : Nat -> Fin n -> Nat) ->
      Initial initial process ->
      Transition process ->
      Exists Nat
        (\ t ->
          Not (Continue (process t))
          and
          ((i : Fin n) ->
            process t i == final i)))
