-- Statement-only formalization of Logipedia corpus artifact nat.le_plus_b
-- (catalog title "nat.le_plus_b"): if a natural number plus an addend is at
-- most an upper bound, then the original number is at most that bound. This
-- file contains no proof.

{-# OPTIONS --safe #-}

module le_plus_b where

open import Agda.Builtin.Nat using (Nat; suc; _+_)

infix 4 _<=_

data _<=_ : Nat -> Nat -> Set where
  le-refl : {n : Nat} -> n <= n
  le-step : {n m : Nat} -> n <= m -> n <= suc m

le-plus-b : Set
le-plus-b =
  (b n m : Nat) ->
  (n + b) <= m ->
  n <= m
