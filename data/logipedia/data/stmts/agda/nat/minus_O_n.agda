-- Statement-only formalization of Logipedia corpus artifact nat.minus_O_n
-- (catalog title "nat.minus_O_n"): zero minus any natural number is zero.
-- This file contains no proof.

{-# OPTIONS --safe #-}

module minus_O_n where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat; zero; _-_)

minus-O-n : Set
minus-O-n =
  (n : Nat) ->
  zero ≡ zero - n
