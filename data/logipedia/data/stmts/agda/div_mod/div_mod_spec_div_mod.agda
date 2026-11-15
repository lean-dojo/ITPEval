-- Statement-only formalization of Logipedia corpus artifact
-- div_mod.div_mod_spec_div_mod (catalog title
-- "div_mod.div_mod_spec_div_mod"): for every natural dividend and positive
-- natural divisor, the fuel-defined quotient and remainder satisfy the
-- remainder bound and quotient-remainder decomposition. This file contains no proof.

{-# OPTIONS --safe #-}

module div_mod_spec_div_mod where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _-_; _*_)

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

record DivModSpec (n m q r : Nat) : Set where
  constructor div-mod-spec-intro
  field
    remainder-bound : r < m
    quotient-remainder-decomposition : n ≡ q * m + r

div-mod-spec-div-mod : Set
div-mod-spec-div-mod =
  (n m : Nat) ->
  zero < m ->
  DivModSpec n m (naturalDiv n m) (naturalMod n m)
