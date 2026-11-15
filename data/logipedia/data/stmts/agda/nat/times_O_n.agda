-- Statement-only formalization of Logipedia corpus artifact nat.times_O_n
-- (catalog title "nat.times_O_n"): multiplying zero on the left by any
-- natural number yields zero. This file contains no proof.

{-# OPTIONS --safe #-}

module times_O_n where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat; zero; _*_)

times-O-n : Set
times-O-n =
  (n : Nat) ->
  zero ≡ zero * n
