-- Statement-only formalization of Logipedia corpus artifact nat.associative_plus
-- (catalog title "nat.associative_plus"): addition on the natural numbers is
-- associative. This file contains no proof.

{-# OPTIONS --safe #-}

module associative_plus where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat; _+_)

associative-plus : Set
associative-plus =
  (x y z : Nat) ->
  (x + y) + z ≡ x + (y + z)
