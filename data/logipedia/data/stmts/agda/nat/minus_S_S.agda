-- Statement-only formalization of Logipedia corpus artifact nat.minus_S_S
-- (catalog title "nat.minus_S_S"): subtracting two successor natural numbers
-- gives the same truncated difference as subtracting their predecessors. This
-- file contains no proof.

{-# OPTIONS --safe #-}

module minus_S_S where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat; suc; _-_)

minus-S-S : Set
minus-S-S =
  (n m : Nat) ->
  suc n - suc m ≡ n - m
