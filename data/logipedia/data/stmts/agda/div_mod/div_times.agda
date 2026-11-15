-- Statement-only formalization of Logipedia corpus artifact
-- div_mod.div_times (catalog title "div_mod.div_times"): dividing the product
-- of two natural numbers by its positive second factor yields the first
-- factor, using the module's fuel-defined natural-number division. This file
-- contains no proof.

{-# OPTIONS --safe #-}

module div_times where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _-_; _*_)

infix 4 _<_

data _<_ : Nat -> Nat -> Set where
  zero<suc : {n : Nat} -> zero < suc n
  suc<suc : {m n : Nat} -> m < n -> suc m < suc n

leb : Nat -> Nat -> Bool
leb zero n = true
leb (suc m) zero = false
leb (suc m) (suc n) = leb m n

div-aux : Nat -> Nat -> Nat -> Nat
div-aux zero n m = zero
div-aux (suc p) n m with leb n m
... | true = zero
... | false = suc (div-aux p (n - suc m) m)

naturalDiv : Nat -> Nat -> Nat
naturalDiv n zero = suc n
naturalDiv n (suc m) = div-aux n n m

div-times : Set
div-times =
  (a b : Nat) ->
  zero < b ->
  naturalDiv (a * b) b ≡ a
