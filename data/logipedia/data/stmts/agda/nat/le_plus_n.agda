-- Statement-only formalization of Logipedia corpus artifact nat.le_plus_n
-- (catalog title "nat.le_plus_n"): every natural number is less than or equal
-- to the result of adding another natural number on its left. This file
-- contains no proof.

{-# OPTIONS --safe #-}

module le_plus_n where

open import Agda.Builtin.Nat using (Nat; suc; _+_)

infix 4 _<=_

data _<=_ : Nat -> Nat -> Set where
  le-refl : {n : Nat} -> n <= n
  le-step : {n m : Nat} -> n <= m -> n <= suc m

le-plus-n : Set
le-plus-n =
  (n m : Nat) ->
  m <= n + m
