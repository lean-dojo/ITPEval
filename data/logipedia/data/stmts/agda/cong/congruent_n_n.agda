-- Statement-only formalization of Logipedia corpus artifact
-- cong.congruent_n_n (catalog title "cong.congruent_n_n"): every natural
-- number is congruent to itself modulo every natural modulus. This file
-- contains no proof.

{-# OPTIONS --safe #-}

module congruent_n_n where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using
  (Nat; zero; suc; div-helper; mod-helper)

naturalMod : Nat -> Nat -> Nat
naturalMod numerator zero =
  numerator
naturalMod numerator (suc denominator) =
  mod-helper zero denominator numerator denominator

Congruent : Nat -> Nat -> Nat -> Set
Congruent n m p =
  naturalMod n p ≡ naturalMod m p

congruent-n-n : Set
congruent-n-n =
  (n p : Nat) ->
  Congruent n n p
