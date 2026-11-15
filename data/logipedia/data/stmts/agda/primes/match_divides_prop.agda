-- Statement-only formalization of Logipedia corpus artifact
-- primes.match_divides_prop (catalog title "primes.match_divides_prop"):
-- the proposition-valued elimination principle for natural-number
-- divisibility, exposing a quotient and its multiplication equation.
-- This file contains no proof.

{-# OPTIONS --safe #-}

module match_divides_prop where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat; _*_)

module Statement
  (Divides : Nat -> Nat -> Set) where

  match-divides-prop : Set₁
  match-divides-prop =
    (n m : Nat) ->
    (return : Set) ->
    ((q : Nat) -> m ≡ n * q -> return) ->
    Divides n m ->
    return
