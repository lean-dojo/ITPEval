-- Statement-only formalization of Logipedia corpus artifact nat.minus_plus_plus_l
-- (catalog title "nat.minus_plus_plus_l"): adding the same natural number to
-- both arguments of truncated subtraction leaves the difference unchanged.
-- This file contains no proof.

{-# OPTIONS --safe #-}

module minus_plus_plus_l where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat; _+_; _-_)

minus-plus-plus-l : Set
minus-plus-plus-l =
  (x y h : Nat) ->
  (x + h) - (y + h) ≡ x - y
