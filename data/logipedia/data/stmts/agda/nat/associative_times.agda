-- Statement-only formalization of Logipedia corpus artifact nat.associative_times
-- (catalog title "nat.associative_times"): multiplication on the natural
-- numbers is associative. This file contains no proof.

{-# OPTIONS --safe #-}

module associative_times where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat; _*_)

associative-times : Set
associative-times =
  (x y z : Nat) ->
  (x * y) * z ≡ x * (y * z)
