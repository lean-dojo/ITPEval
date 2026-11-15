-- Statement-only formalization of Logipedia corpus artifact nat.minus_plus_m_m
-- (catalog title "nat.minus_plus_m_m"): adding a natural number and then
-- subtracting that same number returns the original. This file contains no
-- proof.

{-# OPTIONS --safe #-}

module minus_plus_m_m where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat; _+_; _-_)

minus-plus-m-m : Set
minus-plus-m-m =
  (n m : Nat) ->
  n ≡ (n + m) - m
