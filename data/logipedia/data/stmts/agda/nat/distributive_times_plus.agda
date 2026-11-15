-- Statement-only formalization of Logipedia corpus artifact
-- nat.distributive_times_plus (catalog title "nat.distributive_times_plus"):
-- multiplication on the natural numbers distributes over addition on the
-- left. This file contains no proof.

{-# OPTIONS --safe #-}

module distributive_times_plus where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat; _+_; _*_)

distributive-times-plus : Set
distributive-times-plus =
  (a b c : Nat) ->
  a * (b + c) ≡ (a * b) + (a * c)
