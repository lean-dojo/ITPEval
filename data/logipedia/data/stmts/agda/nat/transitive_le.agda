-- Statement-only formalization of Logipedia corpus artifact nat.transitive_le
-- (catalog title "nat.transitive_le"): natural-number less-than-or-equal is
-- transitive. This file contains no proof.

{-# OPTIONS --safe #-}

module transitive_le where

open import Agda.Builtin.Nat using (Nat; suc)

infix 4 _<=_

data _<=_ : Nat -> Nat -> Set where
  le-refl : {n : Nat} -> n <= n
  le-step : {n m : Nat} -> n <= m -> n <= suc m

transitive-le : Set
transitive-le =
  (a b c : Nat) ->
  a <= b ->
  b <= c ->
  a <= c
