-- Statement-only formalization of Logipedia corpus artifact nat.le_S
-- (catalog title "nat.le_S"): natural-number less-than-or-equal is preserved
-- when the upper bound is replaced by its successor. This file contains no proof.

{-# OPTIONS --safe #-}

module le_S where

open import Agda.Builtin.Nat using (Nat; zero; suc)

infix 4 _<=_

data _<=_ : Nat -> Nat -> Set where
  zero<=   : {n : Nat} -> zero <= n
  suc<=suc : {m n : Nat} -> m <= n -> suc m <= suc n

le-S : Set
le-S =
  (n m : Nat) ->
  n <= m ->
  n <= suc m
