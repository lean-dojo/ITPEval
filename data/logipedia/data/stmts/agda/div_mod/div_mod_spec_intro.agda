-- Statement-only formalization of Logipedia corpus artifact
-- div_mod.div_mod_spec_intro (catalog title "div_mod.div_mod_spec_intro"):
-- for natural numbers n, m, q, and r, a remainder bound r < m and the
-- decomposition n = q * m + r imply the division-with-remainder specification.
-- This file contains no proof.

{-# OPTIONS --safe #-}

module div_mod_spec_intro where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)

infix 4 _<_

data _<_ : Nat -> Nat -> Set where
  zero<suc : {n : Nat} -> zero < suc n
  suc<suc : {m n : Nat} -> m < n -> suc m < suc n

module Statement
  (DivModSpec : Nat -> Nat -> Nat -> Nat -> Set) where

  div-mod-spec-intro : Set
  div-mod-spec-intro =
    (n m q r : Nat) ->
    r < m ->
    n ≡ q * m + r ->
    DivModSpec n m q r
