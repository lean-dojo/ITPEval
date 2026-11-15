-- Statement-only formalization of Logipedia corpus artifact
-- primes.dividesb_false_to_not_divides (catalog title
-- "primes.dividesb_false_to_not_divides"): if the modulo-based Boolean
-- divisibility test on two natural numbers returns false, then the first
-- natural number does not divide the second. This file contains no proof.

{-# OPTIONS --safe #-}

module dividesb_false_to_not_divides where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _-_; _*_)
open import Agda.Builtin.Sigma using (Σ)

infix 4 Divides

data Empty : Set where

Not : Set -> Set
Not A =
  A -> Empty

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

dividesb-false-to-not-divides : Set
dividesb-false-to-not-divides =
  (n m : Nat) ->
  dividesb n m ≡ false ->
  Not (Divides n m)
