-- Statement-only formalization of Logipedia corpus artifact nat.minus_minus_comm
-- (catalog title "nat.minus_minus_comm"): the order of two successive
-- truncated subtractions from a natural number does not matter. This file
-- contains no proof.

{-# OPTIONS --safe #-}

module minus_minus_comm where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat; _-_)

minus-minus-comm : Set
minus-minus-comm =
  (a b c : Nat) ->
  (a - b) - c ≡ (a - c) - b
