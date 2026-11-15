-- Statement-only formalization of Logipedia corpus artifact nat.times_n_O
-- (catalog title "nat.times_n_O"): multiplying any natural number by zero on
-- the right yields zero. This file contains no proof.

{-# OPTIONS --safe #-}

module times_n_O where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat; zero; _*_)

times-n-O : Set
times-n-O =
  (n : Nat) ->
  zero ≡ n * zero
