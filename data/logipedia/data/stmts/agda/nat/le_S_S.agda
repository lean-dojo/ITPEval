-- Statement-only formalization of Logipedia corpus artifact nat.le_S_S
-- (catalog title "nat.le_S_S"): natural-number less-than-or-equal is preserved
-- when successor is applied to both bounds. This file contains no proof.

{-# OPTIONS --safe #-}

module le_S_S where

open import Agda.Builtin.Nat using (Nat; zero; suc)

infix 4 _<=_

data _<=_ : Nat -> Nat -> Set where
  zero<=   : {n : Nat} -> zero <= n
  suc<=suc : {m n : Nat} -> m <= n -> suc m <= suc n

le-S-S : Set
le-S-S =
  (n m : Nat) ->
  n <= m ->
  suc n <= suc m
