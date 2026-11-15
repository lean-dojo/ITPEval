-- Statement-only formalization of Logipedia corpus artifact nat.times_Sn_m
-- (catalog title "nat.times_Sn_m"): for all natural numbers n and m, adding m
-- to n times m equals multiplying the successor of n by m. This file contains
-- no proof.

{-# OPTIONS --safe #-}

module times_Sn_m where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat; suc; _+_; _*_)

times-Sn-m : Set
times-Sn-m =
  (n m : Nat) ->
  m + (n * m) ≡ (suc n) * m
