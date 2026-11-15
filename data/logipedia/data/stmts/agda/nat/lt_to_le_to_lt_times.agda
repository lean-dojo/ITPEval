-- Statement-only formalization of Logipedia corpus artifact
-- nat.lt_to_le_to_lt_times (catalog title "nat.lt_to_le_to_lt_times"):
-- multiplying a strict natural-number inequality and a non-strict one, whose
-- upper bound is positive, yields a strict inequality. This file contains no
-- proof.

{-# OPTIONS --safe #-}

module lt_to_le_to_lt_times where

open import Agda.Builtin.Nat using (Nat; zero; suc; _*_)

infix 4 _<=_ _<_

data _<=_ : Nat -> Nat -> Set where
  zero<=   : {n : Nat} -> zero <= n
  suc<=suc : {m n : Nat} -> m <= n -> suc m <= suc n

_<_ : Nat -> Nat -> Set
m < n =
  suc m <= n

lt-to-le-to-lt-times : Set
lt-to-le-to-lt-times =
  (n m p q : Nat) ->
  n < m ->
  p <= q ->
  zero < q ->
  (n * p) < (m * q)
