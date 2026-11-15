-- Statement-only formalization of Logipedia corpus artifact
-- cong.mod_times (catalog title "cong.mod_times"): reducing a product modulo
-- a positive natural modulus is unchanged when both factors are first reduced
-- modulo that modulus. This file contains no proof.

{-# OPTIONS --safe #-}

module mod_times where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using
  (Nat; zero; suc; _*_; mod-helper)

infix 4 _<_

data _<_ : Nat -> Nat -> Set where
  zero<suc : {n : Nat} -> zero < suc n
  suc<suc : {m n : Nat} -> m < n -> suc m < suc n

naturalMod : Nat -> Nat -> Nat
naturalMod numerator zero =
  numerator
naturalMod numerator (suc denominator) =
  mod-helper zero denominator numerator denominator

mod-times : Set
mod-times =
  (n m p : Nat) ->
  zero < p ->
  naturalMod (n * m) p ≡
    naturalMod (naturalMod n p * naturalMod m p) p
