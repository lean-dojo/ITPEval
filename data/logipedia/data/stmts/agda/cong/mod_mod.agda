-- Statement-only formalization of Logipedia corpus artifact
-- cong.mod_mod (catalog title "cong.mod_mod"): taking the natural-number
-- remainder modulo a positive modulus is idempotent. This file contains no proof.

{-# OPTIONS --safe #-}

module mod_mod where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat; zero; suc; mod-helper)

infix 4 _<_

data _<_ : Nat -> Nat -> Set where
  zero<suc : {n : Nat} -> zero < suc n
  suc<suc : {m n : Nat} -> m < n -> suc m < suc n

naturalMod : Nat -> Nat -> Nat
naturalMod numerator zero =
  numerator
naturalMod numerator (suc denominator) =
  mod-helper zero denominator numerator denominator

mod-mod : Set
mod-mod =
  (n p : Nat) ->
  zero < p ->
  naturalMod n p ≡ naturalMod (naturalMod n p) p
