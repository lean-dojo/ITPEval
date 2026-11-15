-- Statement-only formalization of Logipedia corpus artifact nat.pred_Sn
-- (catalog title "nat.pred_Sn"): every natural number equals the predecessor
-- of its successor. This file contains no proof.

{-# OPTIONS --safe #-}

module pred_Sn where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat; zero; suc)

pred : Nat -> Nat
pred zero =
  zero
pred (suc n) =
  n

pred-Sn : Set
pred-Sn =
  (n : Nat) ->
  n ≡ pred (suc n)
