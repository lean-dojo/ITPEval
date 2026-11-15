-- Statement-only formalization of Logipedia corpus artifact nat.injective_plus_r
-- (catalog title "nat.injective_plus_r"): adding a fixed natural number on the
-- left defines an injective function. This file contains no proof.

{-# OPTIONS --safe #-}

module injective_plus_r where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat; _+_)

injective-plus-r : Set
injective-plus-r =
  (n x y : Nat) ->
  n + x ≡ n + y ->
  x ≡ y
