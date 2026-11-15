-- Statement-only formalization of Logipedia corpus artifact
-- cong.eq_times_plus_to_congruent (catalog title "cong.eq_times_plus_to_congruent"):
-- a natural number equal to a multiple of a positive modulus plus another
-- natural number is congruent to that number modulo the modulus. This file
-- contains no proof.

{-# OPTIONS --safe #-}

module eq_times_plus_to_congruent where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using
  (Nat; zero; suc; _+_; _*_; mod-helper)

infix 4 _<_ Congruent

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

eq-times-plus-to-congruent : Set
eq-times-plus-to-congruent =
  (n m p r : Nat) ->
  zero < p ->
  n ≡ (r * p) + m ->
  Congruent n m p
