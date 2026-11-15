-- Statement-only formalization of Logipedia corpus artifact
-- primes.divides_to_div_mod_spec (catalog title
-- "primes.divides_to_div_mod_spec"): a positive natural divisor of a natural
-- number yields a division specification with the computed quotient and zero
-- remainder. This file contains no proof.

{-# OPTIONS --safe #-}

module divides_to_div_mod_spec where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _-_; _*_)
open import Agda.Builtin.Sigma using (Σ)

infix 4 _<_ Divides

data _<_ : Nat -> Nat -> Set where
  zero<suc : {n : Nat} -> zero < suc n
  suc<suc : {m n : Nat} -> m < n -> suc m < suc n

Divides : Nat -> Nat -> Set
Divides divisor dividend =
  Σ Nat (\ quotient -> dividend ≡ divisor * quotient)

leb : Nat -> Nat -> Bool
leb zero n = true
leb (suc m) zero = false
leb (suc m) (suc n) = leb m n

div-aux : Nat -> Nat -> Nat -> Nat
div-aux zero n m = zero
div-aux (suc p) n m with leb n m
... | true = zero
... | false = suc (div-aux p (n - suc m) m)

naturalDiv : Nat -> Nat -> Nat
naturalDiv n zero = suc n
naturalDiv n (suc m) = div-aux n n m

record DivModSpec (n m q r : Nat) : Set where
  constructor div-mod-spec-intro
  field
    remainder-bound : r < m
    quotient-remainder-decomposition : n ≡ q * m + r

divides-to-div-mod-spec : Set
divides-to-div-mod-spec =
  (n m : Nat) ->
  zero < n ->
  Divides n m ->
  DivModSpec m n (naturalDiv m n) zero
