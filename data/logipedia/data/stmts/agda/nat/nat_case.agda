-- Statement-only formalization of Logipedia corpus artifact nat.nat_case
-- (catalog title "nat.nat_case"): the equality-guarded zero-or-successor case
-- principle for a predicate on natural numbers. This file contains no proof.

{-# OPTIONS --safe #-}

module nat_case where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat; zero; suc)

nat-case : Set₁
nat-case =
  (n : Nat) ->
  (P : Nat -> Set) ->
  (n ≡ zero -> P zero) ->
  ((m : Nat) -> n ≡ suc m -> P (suc m)) ->
  P n
