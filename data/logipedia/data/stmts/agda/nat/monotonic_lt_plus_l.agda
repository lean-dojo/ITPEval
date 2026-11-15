-- Statement-only formalization of Logipedia corpus artifact
-- nat.monotonic_lt_plus_l (catalog title "nat.monotonic_lt_plus_l"):
-- adding a fixed natural number on the right is monotone for strict natural
-- number order. This file contains no proof.

{-# OPTIONS --safe #-}

module monotonic_lt_plus_l where

open import Agda.Builtin.Nat using (Nat; suc; _+_)

infix 4 _<=_ _<_

data _<=_ : Nat -> Nat -> Set where
  le-refl : {n : Nat} -> n <= n
  le-step : {n m : Nat} -> n <= m -> n <= suc m

_<_ : Nat -> Nat -> Set
m < n =
  suc m <= n

monotonic-lt-plus-l : Set
monotonic-lt-plus-l =
  (n x y : Nat) ->
  x < y ->
  (x + n) < (y + n)
