-- Statement-only formalization of Logipedia corpus artifact
-- cong.divides_to_congruent (catalog title "cong.divides_to_congruent"):
-- if a positive modulus divides the truncated difference of ordered natural
-- numbers, then those numbers are congruent modulo that modulus. This file
-- contains no proof.

{-# OPTIONS --safe #-}

module divides_to_congruent where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using
  (Nat; zero; suc; _-_; _*_; mod-helper)
open import Agda.Builtin.Sigma using (Σ)

infix 4 _<_ _≤_ Congruent Divides

data _<_ : Nat -> Nat -> Set where
  zero<suc : {n : Nat} -> zero < suc n
  suc<suc : {m n : Nat} -> m < n -> suc m < suc n

data _≤_ : Nat -> Nat -> Set where
  zero≤ : {n : Nat} -> zero ≤ n
  suc≤suc : {m n : Nat} -> m ≤ n -> suc m ≤ suc n

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

divides-to-congruent : Set
divides-to-congruent =
  (n m p : Nat) ->
  zero < p ->
  m ≤ n ->
  Divides p (n - m) ->
  Congruent n m p
