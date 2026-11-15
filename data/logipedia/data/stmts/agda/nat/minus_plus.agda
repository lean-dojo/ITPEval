-- Statement-only formalization of Logipedia corpus artifact nat.minus_plus
-- (catalog title "nat.minus_plus"): two successive truncated subtractions
-- equal subtraction by the sum of the two subtrahends. This file contains no
-- proof.

{-# OPTIONS --safe #-}

module minus_plus where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat; _+_; _-_)

minus-plus : Set
minus-plus =
  (n m p : Nat) ->
  (n - m) - p ≡ n - (m + p)
