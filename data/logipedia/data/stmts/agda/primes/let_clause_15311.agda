-- Statement-only formalization of Logipedia corpus artifact
-- primes.let_clause_15311 (catalog title "primes.let_clause_15311"): a positive
-- natural number equal to n times the successor of p equals n plus n times p,
-- under the source divisibility hypothesis and quantified d. This file contains no proof.

{-# OPTIONS --safe #-}

module let-clause-15311 where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)
open import Agda.Builtin.Sigma using (Σ)

infix 4 _<_ Divides

data _<_ : Nat -> Nat -> Set where
  zero<suc : {n : Nat} -> zero < suc n
  suc<suc : {m n : Nat} -> m < n -> suc m < suc n

Divides : Nat -> Nat -> Set
Divides divisor dividend =
  Σ Nat (\ quotient -> dividend ≡ divisor * quotient)

let-clause-15311 : Set
let-clause-15311 =
  (n m : Nat) ->
  zero < m ->
  Divides n m ->
  (d p : Nat) ->
  m ≡ n * suc p ->
  m ≡ n + n * p
