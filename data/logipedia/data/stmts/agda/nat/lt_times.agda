-- Statement-only formalization of Logipedia corpus artifact nat.lt_times
-- (catalog title "nat.lt_times"): multiplying two strictly ordered pairs of
-- natural numbers preserves strict order. This file contains no proof.

{-# OPTIONS --safe #-}

module lt_times where

open import Agda.Builtin.Nat using (Nat; suc; _*_)

infix 4 _<=_ _<_

data _<=_ : Nat -> Nat -> Set where
  le-refl : {n : Nat} -> n <= n
  le-step : {n m : Nat} -> n <= m -> n <= suc m

_<_ : Nat -> Nat -> Set
m < n =
  suc m <= n

lt-times : Set
lt-times =
  (n m p q : Nat) ->
  n < m ->
  p < q ->
  (n * p) < (m * q)
