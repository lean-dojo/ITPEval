-- Statement-only formalization of Logipedia corpus artifact nat.plus_n_O
-- (catalog title "nat.plus_n_O"): adding zero on the right leaves every
-- natural number unchanged. This file contains no proof.

{-# OPTIONS --safe #-}

module plus_n_O where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat; zero; _+_)

plus-n-O : Set
plus-n-O =
  (n : Nat) ->
  n ≡ n + zero
