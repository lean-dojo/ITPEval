-- Statement-only formalization of PutnamBench corpus artifact putnam_2025_b3
-- (putnambench__agda__putnam_2025_b3): every nonempty set of positive
-- integers closed under positive divisors of 2025^n - 15^n contains exactly
-- all positive integers. This file contains no proof.

{-# OPTIONS --safe #-}

module Putnam2025B3 where

open import Agda.Builtin.Equality renaming (_≡_ to _==_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _-_; _*_)

infix 4 _divides_
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

data Positive : Nat -> Set where
  positive : {n : Nat} -> Positive (suc n)

record _divides_ (divisor dividend : Nat) : Set where
  constructor quotient-witness
  field
    quotient : Nat
    equation : dividend == divisor * quotient

power : Nat -> Nat -> Nat
power base zero =
  suc zero
power base (suc exponent) =
  base * power base exponent

SameSet : (Nat -> Set) -> (Nat -> Set) -> Set
SameSet left right =
  ((n : Nat) -> left n -> right n)
  and
  ((n : Nat) -> right n -> left n)

putnam-2025-b3 : Set1
putnam-2025-b3 =
  (S : Nat -> Set) ->
  Exists Nat S ->
  ((n : Nat) -> S n -> Positive n) ->
  ((n : Nat) ->
    S n ->
    (d : Nat) ->
    Positive d ->
    d divides (power 2025 n - power 15 n) ->
    S d) ->
  SameSet S Positive
