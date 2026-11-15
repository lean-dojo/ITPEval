-- Statement-only formalization of Logipedia corpus artifact
-- primes.decidable_divides (catalog title "primes.decidable_divides"):
-- divisibility of natural numbers is decidable for every divisor and dividend.
-- This file contains no proof.

{-# OPTIONS --safe #-}

module decidable_divides where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat; _*_)
open import Agda.Builtin.Sigma using (Σ)

infix 4 Divides

data Bottom : Set where

Not : Set -> Set
Not A =
  A -> Bottom

data Either (A B : Set) : Set where
  left  : A -> Either A B
  right : B -> Either A B

Divides : Nat -> Nat -> Set
Divides divisor dividend =
  Σ Nat (\ quotient -> dividend ≡ divisor * quotient)

Decidable : Set -> Set
Decidable A =
  Either A (Not A)

decidable-divides : Set
decidable-divides =
  (n m : Nat) ->
  Decidable (Divides n m)
