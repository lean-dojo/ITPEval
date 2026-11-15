-- Statement-only formalization of Logipedia corpus artifact
-- gcd.divides_mod_to_divides (catalog title
-- "gcd.divides_mod_to_divides"): if a natural number divides the remainder
-- of m modulo a positive n and also divides n, then it divides m. This file
-- contains no proof.

{-# OPTIONS --safe #-}

module divides_mod_to_divides where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _-_; _*_)
open import Agda.Builtin.Sigma using (Σ)

infix 4 _≤_ _<_ Divides

data _≤_ : Nat -> Nat -> Set where
  zero≤ : {n : Nat} -> zero ≤ n
  suc≤suc : {m n : Nat} -> m ≤ n -> suc m ≤ suc n

_<_ : Nat -> Nat -> Set
m < n = suc m ≤ n

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

divides-mod-to-divides : Set
divides-mod-to-divides =
  (p m n : Nat) ->
  zero < n ->
  Divides p (naturalMod m n) ->
  Divides p n ->
  Divides p m
