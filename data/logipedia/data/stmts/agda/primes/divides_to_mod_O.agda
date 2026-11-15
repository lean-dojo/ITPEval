-- Statement-only formalization of Logipedia corpus artifact
-- primes.divides_to_mod_O (catalog title "primes.divides_to_mod_O"): if a
-- positive natural number divides another natural number, then the latter has
-- zero remainder modulo the former. This file contains no proof.

{-# OPTIONS --safe #-}

module divides_to_mod_O where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _-_; _*_)
open import Agda.Builtin.Sigma using (Σ)

infix 4 _<_ Divides

data _<_ : Nat -> Nat -> Set where
  zero<suc : {n : Nat} -> zero < suc n
  suc<suc  : {m n : Nat} -> m < n -> suc m < suc n

Divides : Nat -> Nat -> Set
Divides divisor dividend =
  Σ Nat (\ quotient -> dividend ≡ divisor * quotient)

leb : Nat -> Nat -> Bool
leb zero n = true
leb (suc m) zero = false
leb (suc m) (suc n) = leb m n

mod-aux : Nat -> Nat -> Nat -> Nat
mod-aux zero n m = n
mod-aux (suc p) n m with leb n m
... | true = n
... | false = mod-aux p (n - suc m) m

naturalMod : Nat -> Nat -> Nat
naturalMod n zero = n
naturalMod n (suc m) = mod-aux n n m

divides-to-mod-O : Set
divides-to-mod-O =
  (n m : Nat) ->
  zero < n ->
  Divides n m ->
  naturalMod m n ≡ zero
