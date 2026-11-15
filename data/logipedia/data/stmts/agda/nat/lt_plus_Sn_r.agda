-- Statement-only formalization of Logipedia corpus artifact nat.lt_plus_Sn_r
-- (catalog title "nat.lt_plus_Sn_r"): every natural number is strictly less
-- than the sum of itself, another natural number, and a positive successor.
-- This file contains no proof.

{-# OPTIONS --safe #-}

module lt_plus_Sn_r where

open import Agda.Builtin.Nat using (Nat; suc; _+_)

infix 4 _<=_ _<_

data _<=_ : Nat -> Nat -> Set where
  le-refl : {n : Nat} -> n <= n
  le-step : {n m : Nat} -> n <= m -> n <= suc m

_<_ : Nat -> Nat -> Set
m < n =
  suc m <= n

lt-plus-Sn-r : Set
lt-plus-Sn-r =
  (a x n : Nat) ->
  a < ((a + x) + suc n)
