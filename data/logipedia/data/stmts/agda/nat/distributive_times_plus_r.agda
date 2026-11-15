-- Statement-only formalization of Logipedia corpus artifact
-- nat.distributive_times_plus_r (catalog title "nat.distributive_times_plus_r"):
-- multiplying a sum of natural numbers on the right distributes over that
-- sum. This file contains no proof.

{-# OPTIONS --safe #-}

module distributive_times_plus_r where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat; _+_; _*_)

distributive-times-plus-r : Set
distributive-times-plus-r =
  (a b c : Nat) ->
  (b + c) * a ≡ (b * a) + (c * a)
