-- Statement-only formalization of Logipedia corpus artifact
-- nat.le_plus_to_minus_r (catalog title "nat.le_plus_to_minus_r"): if the sum
-- of two natural numbers is at most a third, then the first is at most the
-- third's truncated difference with the second. This file contains no proof.

{-# OPTIONS --safe #-}

module le_plus_to_minus_r where

open import Agda.Builtin.Nat using (Nat; suc; _+_; _-_)

infix 4 _<=_

data _<=_ : Nat -> Nat -> Set where
  le-refl : {n : Nat} -> n <= n
  le-step : {n m : Nat} -> n <= m -> n <= suc m

le-plus-to-minus-r : Set
le-plus-to-minus-r =
  (a b c : Nat) ->
  (a + b) <= c ->
  a <= (c - b)
