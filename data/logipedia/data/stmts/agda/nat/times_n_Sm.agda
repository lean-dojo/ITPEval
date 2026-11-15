-- Statement-only formalization of Logipedia corpus artifact nat.times_n_Sm
-- (catalog title "nat.times_n_Sm"): for all natural numbers n and m, adding n
-- to n times m equals n times the successor of m. This file contains no proof.

{-# OPTIONS --safe #-}

module times_n_Sm where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat; suc; _+_; _*_)

times-n-Sm : Set
times-n-Sm =
  (n m : Nat) ->
  n + (n * m) ≡ n * suc m
