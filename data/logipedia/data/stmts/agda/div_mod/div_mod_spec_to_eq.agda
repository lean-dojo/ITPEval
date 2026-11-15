-- Statement-only formalization of Logipedia corpus artifact
-- div_mod.div_mod_spec_to_eq (catalog title "div_mod.div_mod_spec_to_eq"):
-- two division-with-remainder specifications for the same natural dividend
-- and divisor have equal quotients. This file contains no proof.

{-# OPTIONS --safe #-}

module div_mod_spec_to_eq where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)

infix 4 _<_

data _<_ : Nat -> Nat -> Set where
  zero<suc : {n : Nat} -> zero < suc n
  suc<suc : {m n : Nat} -> m < n -> suc m < suc n

record DivModSpec (a b q r : Nat) : Set where
  constructor div-mod-spec-intro
  field
    remainder-bound : r < b
    quotient-remainder-decomposition : a ≡ q * b + r

div-mod-spec-to-eq : Set
div-mod-spec-to-eq =
  (a b q r q1 r1 : Nat) ->
  DivModSpec a b q r ->
  DivModSpec a b q1 r1 ->
  q ≡ q1
