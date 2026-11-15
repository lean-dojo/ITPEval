-- Statement-only formalization of Logipedia corpus artifact
-- cong.congruent_to_divides (catalog title "cong.congruent_to_divides"):
-- congruent natural numbers modulo a positive modulus have a truncated
-- difference divisible by that modulus. This file contains no proof.

{-# OPTIONS --safe #-}

module congruent_to_divides where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using
  (Nat; zero; suc; _-_; _*_; div-helper; mod-helper)
open import Agda.Builtin.Sigma using (Σ)

infix 4 _<_ Congruent Divides

data _<_ : Nat -> Nat -> Set where
  zero<suc : {n : Nat} -> zero < suc n
  suc<suc : {m n : Nat} -> m < n -> suc m < suc n

naturalMod : Nat -> Nat -> Nat
naturalMod numerator zero =
  numerator
naturalMod numerator (suc denominator) =
  mod-helper zero denominator numerator denominator

Congruent : Nat -> Nat -> Nat -> Set
Congruent n m p =
  naturalMod n p ≡ naturalMod m p

Divides : Nat -> Nat -> Set
Divides divisor dividend =
  Σ Nat (\ quotient -> dividend ≡ divisor * quotient)

congruent-to-divides : Set
congruent-to-divides =
  (n m p : Nat) ->
  zero < p ->
  Congruent n m p ->
  Divides p (n - m)
