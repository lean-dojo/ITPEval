-- Statement-only formalization of Logipedia corpus artifact nat.minus_n_n
-- (catalog title "nat.minus_n_n"): subtracting any natural number from
-- itself yields zero. This file contains no proof.

{-# OPTIONS --safe #-}

module minus_n_n where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat; zero; _-_)

minus-n-n : Set
minus-n-n =
  (n : Nat) ->
  zero ≡ n - n
