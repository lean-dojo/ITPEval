-- Statement-only formalization of Logipedia corpus artifact
-- nat.lt_to_le_to_lt (catalog title "nat.lt_to_le_to_lt"): natural-number
-- order is compatible when a strict inequality is followed by a non-strict
-- inequality. This file contains no proof.

{-# OPTIONS --safe #-}

module lt_to_le_to_lt where

open import Agda.Builtin.Nat using (Nat; zero; suc)

infix 4 _<=_ _<_

data _<=_ : Nat -> Nat -> Set where
  zero<=   : {n : Nat} -> zero <= n
  suc<=suc : {m n : Nat} -> m <= n -> suc m <= suc n

_<_ : Nat -> Nat -> Set
m < n =
  suc m <= n

lt-to-le-to-lt : Set
lt-to-le-to-lt =
  (n m p : Nat) ->
  n < m ->
  m <= p ->
  n < p
