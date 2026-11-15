-- Statement-only formalization of Logipedia corpus artifact nat.le_n
-- (catalog title "nat.le_n"): natural-number less-than-or-equal is reflexive.
-- This file contains no proof.

{-# OPTIONS --safe #-}

module le_n where

open import Agda.Builtin.Nat using (Nat; zero; suc)

infix 4 _<=_

data _<=_ : Nat -> Nat -> Set where
  zero<=   : {n : Nat} -> zero <= n
  suc<=suc : {m n : Nat} -> m <= n -> suc m <= suc n

le-n : Set
le-n =
  (n : Nat) ->
  n <= n
