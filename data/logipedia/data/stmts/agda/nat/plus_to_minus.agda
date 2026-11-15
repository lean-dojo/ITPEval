-- Statement-only formalization of Logipedia corpus artifact nat.plus_to_minus
-- (catalog title "nat.plus_to_minus"): if a natural number equals the sum of
-- two natural numbers, subtracting the first addend yields the second. This
-- file contains no proof.

{-# OPTIONS --safe #-}

module plus_to_minus where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat; _+_; _-_)

plus-to-minus : Set
plus-to-minus =
  (n m p : Nat) ->
  n ≡ m + p ->
  n - m ≡ p
