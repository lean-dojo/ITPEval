-- Statement-only formalization of Logipedia corpus artifact
-- primes.reflexive_divides (catalog title "primes.reflexive_divides"):
-- natural-number divisibility is reflexive. This file contains no proof.

{-# OPTIONS --safe #-}

module reflexive_divides where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat; _*_)
open import Agda.Builtin.Sigma using (Σ)

infix 4 Divides

Divides : Nat -> Nat -> Set
Divides divisor dividend =
  Σ Nat (\ quotient -> dividend ≡ divisor * quotient)

reflexive-divides : Set
reflexive-divides =
  (n : Nat) ->
  Divides n n
