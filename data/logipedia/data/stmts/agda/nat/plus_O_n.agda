-- Statement-only formalization of Logipedia corpus artifact nat.plus_O_n
-- (catalog title "nat.plus_O_n"): adding zero on the left leaves every
-- natural number unchanged. This file contains no proof.

{-# OPTIONS --safe #-}

module plus_O_n where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat; zero; _+_)

plus-O-n : Set
plus-O-n =
  (n : Nat) ->
  n ≡ zero + n
