-- Statement-only formalization of Logipedia corpus artifact
-- div_mod.match_div_mod_spec_prop (catalog title "div_mod.match_div_mod_spec_prop"):
-- the elimination principle for a natural-number division-with-remainder
-- specification, exposing its remainder bound and quotient decomposition.
-- This file contains no proof.

{-# OPTIONS --safe #-}

module match_div_mod_spec_prop where

open import Agda.Primitive using (Level; lsuc)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)

infix 4 _<_

data _<_ : Nat -> Nat -> Set where
  zero<suc : {n : Nat} -> zero < suc n
  suc<suc : {m n : Nat} -> m < n -> suc m < suc n

module Statement
  {proposition-level : Level}
  (DivModSpec :
    Nat -> Nat -> Nat -> Nat -> Set proposition-level) where

  match-div-mod-spec-prop : Set (lsuc proposition-level)
  match-div-mod-spec-prop =
    (n m q r : Nat) ->
    (return : Set proposition-level) ->
    (r < m -> n ≡ q * m + r -> return) ->
    DivModSpec n m q r ->
    return
