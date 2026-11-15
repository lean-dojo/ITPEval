-- Statement-only formalization of Logipedia corpus artifact
-- primes.prime_to_lt_SO (catalog title "primes.prime_to_lt_SO"): every natural
-- number satisfying the source prime predicate is strictly greater than one.
-- This file contains no proof.

{-# OPTIONS --safe #-}

module prime_to_lt_SO where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _*_)
open import Agda.Builtin.Sigma using (Σ)

infix 4 _<_ Divides

data _<_ : Nat -> Nat -> Set where
  zero<suc : {n : Nat} -> zero < suc n
  suc<suc  : {m n : Nat} -> m < n -> suc m < suc n

record Both (A B : Set) : Set where
  field
    first  : A
    second : B

Divides : Nat -> Nat -> Set
Divides divisor dividend =
  Σ Nat (\ quotient -> dividend ≡ divisor * quotient)

Prime : Nat -> Set
Prime n =
  Both
    (suc zero < n)
    ((m : Nat) ->
      Divides m n ->
      suc zero < m ->
      m ≡ n)

prime-to-lt-SO : Set
prime-to-lt-SO =
  (p : Nat) ->
  Prime p ->
  suc zero < p
