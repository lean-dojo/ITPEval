-- Statement-only formalization of Logipedia corpus artifact
-- nat.distributive_times_minus (catalog title "nat.distributive_times_minus"):
-- multiplication on the natural numbers distributes over truncated
-- subtraction on the left. This file contains no proof.

{-# OPTIONS --safe #-}

module distributive_times_minus where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat; _-_; _*_)

distributive-times-minus : Set
distributive-times-minus =
  (a b c : Nat) ->
  a * (b - c) ≡ (a * b) - (a * c)
