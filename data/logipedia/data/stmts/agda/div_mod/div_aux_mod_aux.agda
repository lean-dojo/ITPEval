-- Statement-only formalization of Logipedia corpus artifact
-- div_mod.div_aux_mod_aux (catalog title "div_mod.div_aux_mod_aux"): the
-- fuel-bounded auxiliary quotient and remainder reconstruct every natural
-- number as quotient times one plus the divisor, plus the remainder. This
-- file contains no proof.

{-# OPTIONS --safe #-}

module div_aux_mod_aux where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _-_; _*_)

leb : Nat -> Nat -> Bool
leb zero n = true
leb (suc m) zero = false
leb (suc m) (suc n) = leb m n

mod-aux : Nat -> Nat -> Nat -> Nat
mod-aux zero n m = n
mod-aux (suc p) n m with leb n m
... | true = n
... | false = mod-aux p (n - suc m) m

div-aux : Nat -> Nat -> Nat -> Nat
div-aux zero n m = zero
div-aux (suc p) n m with leb n m
... | true = zero
... | false = suc (div-aux p (n - suc m) m)

div-aux-mod-aux : Set
div-aux-mod-aux =
  (p n m : Nat) ->
  n ≡ div-aux p n m * suc m + mod-aux p n m
