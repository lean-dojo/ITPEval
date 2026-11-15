-- Statement-only formalization of Logipedia corpus artifact nat.minus_n_O
-- (catalog title "nat.minus_n_O"): subtracting zero from any natural number
-- leaves that natural number unchanged. This file contains no proof.

{-# OPTIONS --safe #-}

module minus_n_O where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat; zero; _-_)

minus-n-O : Set
minus-n-O =
  (n : Nat) ->
  n ≡ n - zero
