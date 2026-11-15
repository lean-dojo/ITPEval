-- Statement-only formalization of Logipedia corpus artifact
-- div_mod.lt_mod_m_m (catalog title "div_mod.lt_mod_m_m"): the remainder of
-- a natural number modulo a positive natural modulus is strictly smaller
-- than that modulus. This file contains no proof.

{-# OPTIONS --safe #-}

module lt_mod_m_m where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Nat using (Nat; zero; suc; _-_)

infix 4 _<_

data _<_ : Nat -> Nat -> Set where
  zero<suc : {n : Nat} -> zero < suc n
  suc<suc : {m n : Nat} -> m < n -> suc m < suc n

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

lt-mod-m-m : Set
lt-mod-m-m =
  (n m : Nat) ->
  zero < m ->
  naturalMod n m < m
