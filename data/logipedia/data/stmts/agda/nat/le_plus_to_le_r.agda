-- Statement-only formalization of Logipedia corpus artifact nat.le_plus_to_le_r
-- (catalog title "nat.le_plus_to_le_r"): natural-number order reflects
-- cancellation of a common addend on the right. This file contains no proof.

{-# OPTIONS --safe #-}

module le_plus_to_le_r where

open import Agda.Builtin.Nat using (Nat; suc; _+_)

infix 4 _<=_

data _<=_ : Nat -> Nat -> Set where
  le-refl : {n : Nat} -> n <= n
  le-step : {n m : Nat} -> n <= m -> n <= suc m

le-plus-to-le-r : Set
le-plus-to-le-r =
  (a n m : Nat) ->
  (n + a) <= (m + a) ->
  n <= m
