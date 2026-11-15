-- Statement-only formalization of Logipedia corpus artifact primes.divides_to_le
-- (catalog title "primes.divides_to_le"): a natural divisor of a positive
-- natural number is at most that number. This file contains no proof.

{-# OPTIONS --safe #-}

module divides_to_le where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _*_)
open import Agda.Builtin.Sigma using (Σ)

infix 4 _<=_ _<_ Divides

data _<=_ : Nat -> Nat -> Set where
  zero<=   : {n : Nat} -> zero <= n
  suc<=suc : {m n : Nat} -> m <= n -> suc m <= suc n

data _<_ : Nat -> Nat -> Set where
  zero<suc : {n : Nat} -> zero < suc n
  suc<suc  : {m n : Nat} -> m < n -> suc m < suc n

Divides : Nat -> Nat -> Set
Divides divisor dividend =
  Σ Nat (\ quotient -> dividend ≡ divisor * quotient)

divides-to-le : Set
divides-to-le =
  (n m : Nat) ->
  zero < m ->
  Divides n m ->
  n <= m
