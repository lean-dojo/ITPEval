-- Statement-only formalization of Logipedia corpus artifact
-- primes.dividesb_true_to_divides (catalog title
-- "primes.dividesb_true_to_divides"): if the modulo-based Boolean
-- divisibility test on two natural numbers returns true, then the first
-- natural number divides the second. This file contains no proof.

{-# OPTIONS --safe #-}

module dividesb_true_to_divides where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _-_; _*_)
open import Agda.Builtin.Sigma using (Σ)

infix 4 Divides

Divides : Nat -> Nat -> Set
Divides divisor dividend =
  Σ Nat (\ quotient -> dividend ≡ divisor * quotient)

leb : Nat -> Nat -> Bool
leb zero n = true
leb (suc m) zero = false
leb (suc m) (suc n) = leb m n

eqb : Nat -> Nat -> Bool
eqb zero zero = true
eqb zero (suc n) = false
eqb (suc m) zero = false
eqb (suc m) (suc n) = eqb m n

mod-aux : Nat -> Nat -> Nat -> Nat
mod-aux zero n m = n
mod-aux (suc p) n m with leb n m
... | true = n
... | false = mod-aux p (n - suc m) m

naturalMod : Nat -> Nat -> Nat
naturalMod n zero = n
naturalMod n (suc m) = mod-aux n n m

dividesb : Nat -> Nat -> Bool
dividesb n m = eqb (naturalMod m n) zero

dividesb-true-to-divides : Set
dividesb-true-to-divides =
  (n m : Nat) ->
  dividesb n m ≡ true ->
  Divides n m
