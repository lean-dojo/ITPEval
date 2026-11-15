-- Statement-only formalization of Logipedia corpus artifact primes.divides_n_O
-- (catalog title "primes.divides_n_O"): every natural number divides zero.
-- This file contains no proof.

{-# OPTIONS --safe #-}

module divides_n_O where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat; zero; _*_)
open import Agda.Builtin.Sigma using (Σ)

infix 4 Divides

Divides : Nat -> Nat -> Set
Divides divisor dividend =
  Σ Nat (\ quotient -> dividend ≡ divisor * quotient)

divides-n-O : Set
divides-n-O =
  (n : Nat) ->
  Divides n zero
