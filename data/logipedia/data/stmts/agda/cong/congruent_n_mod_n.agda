-- Statement-only formalization of Logipedia corpus artifact
-- cong.congruent_n_mod_n (catalog title "cong.congruent_n_mod_n"): every
-- natural number is congruent to its remainder modulo a positive natural
-- modulus. This file contains no proof.

{-# OPTIONS --safe #-}

module congruent_n_mod_n where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using
  (Nat; zero; suc; div-helper; mod-helper)

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

congruent-n-mod-n : Set
congruent-n-mod-n =
  (n p : Nat) ->
  zero < p ->
  Congruent n (naturalMod n p) p
