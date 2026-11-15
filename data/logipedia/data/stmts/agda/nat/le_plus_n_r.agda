-- Statement-only formalization of Logipedia corpus artifact nat.le_plus_n_r
-- (catalog title "nat.le_plus_n_r"): every natural number is less than or
-- equal to itself plus any natural number on the right. This file contains
-- no proof.

{-# OPTIONS --safe #-}

module le_plus_n_r where

open import Agda.Builtin.Nat using (Nat; suc; _+_)

infix 4 _<=_

data _<=_ : Nat -> Nat -> Set where
  le-refl : {n : Nat} -> n <= n
  le-step : {n m : Nat} -> n <= m -> n <= suc m

le-plus-n-r : Set
le-plus-n-r =
  (n m : Nat) ->
  m <= m + n
