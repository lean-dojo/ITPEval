-- Statement-only formalization of Logipedia corpus artifact primes.divides_n_n
-- (catalog title "primes.divides_n_n"): every natural number divides itself.
-- This file contains no proof.

{-# OPTIONS --safe #-}

module divides_n_n where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat; _*_)
open import Agda.Builtin.Sigma using (Σ)

infix 4 Divides

Divides : Nat -> Nat -> Set
Divides divisor dividend =
  Σ Nat (\ quotient -> dividend ≡ divisor * quotient)

divides-n-n : Set
divides-n-n =
  (n : Nat) ->
  Divides n n
