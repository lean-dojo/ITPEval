-- Statement-only formalization of Logipedia corpus artifact nat.times_times
-- (catalog title "nat.times_times"): for all natural numbers x, y, and z,
-- x times (y times z) equals y times (x times z). This file contains no proof.

{-# OPTIONS --safe #-}

module times_times where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat; _*_)

times-times : Set
times-times =
  (x y z : Nat) ->
  x * (y * z) ≡ y * (x * z)
