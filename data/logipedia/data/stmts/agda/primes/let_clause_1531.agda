-- Statement-only formalization of Logipedia corpus artifact
-- primes.let_clause_1531 (catalog title "primes.let_clause_1531"): if a
-- positive natural number equals a natural multiple of zero, then it is zero,
-- under the source divisibility hypothesis. This file contains no proof.

{-# OPTIONS --safe #-}

module let-clause-1531 where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _*_)
open import Agda.Builtin.Sigma using (Σ)

infix 4 _<_ Divides

data _<_ : Nat -> Nat -> Set where
  zero<suc : {n : Nat} -> zero < suc n
  suc<suc : {m n : Nat} -> m < n -> suc m < suc n

Divides : Nat -> Nat -> Set
Divides divisor dividend =
  Σ Nat (\ quotient -> dividend ≡ divisor * quotient)

let-clause-1531 : Set
let-clause-1531 =
  (n m : Nat) ->
  zero < m ->
  Divides n m ->
  (d : Nat) ->
  m ≡ n * zero ->
  m ≡ zero
