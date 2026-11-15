-- Statement-only formalization of Logipedia corpus artifact primes.quotient
-- (catalog title "primes.quotient"): a natural number divides any natural
-- multiple of it. This file contains no proof.

{-# OPTIONS --safe #-}

module quotient where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat; _*_)

module Statement
  (Divides : Nat -> Nat -> Set) where

  quotient : Set
  quotient =
    (n m q : Nat) ->
    m ≡ n * q ->
    Divides n m
