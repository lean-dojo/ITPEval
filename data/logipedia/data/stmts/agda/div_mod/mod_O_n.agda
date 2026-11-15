-- Statement-only formalization of Logipedia corpus artifact
-- div_mod.mod_O_n (catalog title "div_mod.mod_O_n"): zero modulo every
-- natural number is zero, using the module's fuel-defined natural-number
-- remainder. This file contains no proof.

{-# OPTIONS --safe #-}

module mod_O_n where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _-_)

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

mod-O-n : Set
mod-O-n =
  (n : Nat) ->
  naturalMod zero n ≡ zero
