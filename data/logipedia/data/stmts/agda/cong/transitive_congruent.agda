-- Statement-only formalization of Logipedia corpus artifact
-- cong.transitive_congruent (catalog title "cong.transitive_congruent"):
-- congruence of natural numbers modulo any natural modulus is transitive.
-- This file contains no proof.

{-# OPTIONS --safe #-}

module transitive_congruent where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using
  (Nat; zero; suc; mod-helper)

naturalMod : Nat -> Nat -> Nat
naturalMod numerator zero =
  numerator
naturalMod numerator (suc denominator) =
  mod-helper zero denominator numerator denominator

Congruent : Nat -> Nat -> Nat -> Set
Congruent n m p =
  naturalMod n p ≡ naturalMod m p

transitive-congruent : Set
transitive-congruent =
  (p x y z : Nat) ->
  Congruent x y p ->
  Congruent y z p ->
  Congruent x z p
