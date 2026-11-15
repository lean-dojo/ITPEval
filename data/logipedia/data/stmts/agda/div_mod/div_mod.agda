-- Statement-only formalization of Logipedia corpus artifact
-- div_mod.div_mod (catalog title "div_mod.div_mod"): every natural number is
-- its fuel-defined quotient times the divisor plus its corresponding
-- remainder. This file contains no proof.

{-# OPTIONS --safe #-}

module div_mod where

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

naturalMod : Nat -> Nat -> Nat
naturalMod n zero = n
naturalMod n (suc m) = mod-aux n n m

naturalDiv : Nat -> Nat -> Nat
naturalDiv n zero = suc n
naturalDiv n (suc m) = div-aux n n m

div-mod : Set
div-mod =
  (n m : Nat) ->
  n ≡ naturalDiv n m * m + naturalMod n m
