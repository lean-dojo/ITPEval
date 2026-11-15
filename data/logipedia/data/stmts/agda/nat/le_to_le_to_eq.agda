-- Statement-only formalization of Logipedia corpus artifact nat.le_to_le_to_eq
-- (catalog title "nat.le_to_le_to_eq"): antisymmetry of the natural-number
-- less-than-or-equal relation. This file contains no proof.

{-# OPTIONS --safe #-}

module le_to_le_to_eq where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat; suc)

infix 4 _<=_

data _<=_ : Nat -> Nat -> Set where
  le-refl : {n : Nat} -> n <= n
  le-step : {n m : Nat} -> n <= m -> n <= suc m

nat-le-to-le-to-eq : Set
nat-le-to-le-to-eq =
  (n m : Nat) ->
  n <= m ->
  m <= n ->
  n ≡ m
