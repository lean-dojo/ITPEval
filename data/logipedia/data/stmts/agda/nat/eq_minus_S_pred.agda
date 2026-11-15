-- Statement-only formalization of Logipedia corpus artifact nat.eq_minus_S_pred
-- (catalog title "nat.eq_minus_S_pred"): subtracting the successor of a
-- natural number equals the predecessor of subtracting that number.
-- This file contains no proof.

{-# OPTIONS --safe #-}

module eq_minus_S_pred where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _-_)

pred : Nat -> Nat
pred zero =
  zero
pred (suc n) =
  n

eq-minus-S-pred : Set
eq-minus-S-pred =
  (n m : Nat) ->
  n - suc m ≡ pred (n - m)
