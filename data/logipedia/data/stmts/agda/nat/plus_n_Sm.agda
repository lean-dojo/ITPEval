-- Statement-only formalization of Logipedia corpus artifact nat.plus_n_Sm
-- (catalog title "nat.plus_n_Sm"): for all natural numbers n and m, the
-- successor of n + m equals n plus the successor of m. This file contains no proof.

{-# OPTIONS --safe #-}

module plus_n_Sm where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat; suc; _+_)

plus-n-Sm : Set
plus-n-Sm =
  (n m : Nat) ->
  suc (n + m) ≡ n + suc m
