-- Statement-only formalization of Logipedia corpus artifact
-- nat.le_to_lt_to_lt (catalog title "nat.le_to_lt_to_lt"): natural-number
-- order is compatible when a non-strict inequality is followed by a strict
-- inequality. This file contains no proof.

{-# OPTIONS --safe #-}

module le_to_lt_to_lt where

open import Agda.Builtin.Nat using (Nat; zero; suc)

infix 4 _<=_ _<_

data _<=_ : Nat -> Nat -> Set where
  zero<=   : {n : Nat} -> zero <= n
  suc<=suc : {m n : Nat} -> m <= n -> suc m <= suc n

_<_ : Nat -> Nat -> Set
m < n =
  suc m <= n

le-to-lt-to-lt : Set
le-to-lt-to-lt =
  (n m p : Nat) ->
  n <= m ->
  m < p ->
  n < p
