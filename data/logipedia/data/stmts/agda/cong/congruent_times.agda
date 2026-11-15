-- Statement-only formalization of Logipedia corpus artifact
-- cong.congruent_times (catalog title "cong.congruent_times"): multiplication
-- preserves congruence modulo a positive natural modulus. This file contains
-- no proof.

{-# OPTIONS --safe #-}

module congruent_times where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using
  (Nat; zero; suc; _*_; div-helper; mod-helper)

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

congruent-times : Set
congruent-times =
  (n m n1 m1 p : Nat) ->
  zero < p ->
  Congruent n n1 p ->
  Congruent m m1 p ->
  Congruent (n * m) (n1 * m1) p
