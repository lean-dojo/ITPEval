-- Statement-only formalization of Logipedia corpus artifact nat.le_plus
-- (catalog title "nat.le_plus"): natural-number addition is monotone in both
-- arguments. This file contains no proof.

{-# OPTIONS --safe #-}

module le_plus where

open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)

infix 4 _<=_

data _<=_ : Nat -> Nat -> Set where
  le-refl : {n : Nat} -> n <= n
  le-step : {n m : Nat} -> n <= m -> n <= suc m

le-plus : Set
le-plus =
  (n1 n2 m1 m2 : Nat) ->
  n1 <= n2 ->
  m1 <= m2 ->
  (n1 + m1) <= (n2 + m2)
