-- Statement-only formalization of Logipedia corpus artifact nat.lt_to_not_le
-- (catalog title "nat.lt_to_not_le"): a strict natural-number inequality n < m
-- excludes the reverse non-strict inequality m <= n. This file contains no proof.

{-# OPTIONS --safe #-}

module lt_to_not_le where

open import Agda.Builtin.Nat using (Nat; zero; suc)

infix 4 _<=_ _<_

data Bottom : Set where

Not : Set -> Set
Not A =
  A -> Bottom

data _<=_ : Nat -> Nat -> Set where
  zero<=   : {n : Nat} -> zero <= n
  suc<=suc : {m n : Nat} -> m <= n -> suc m <= suc n

_<_ : Nat -> Nat -> Set
m < n =
  suc m <= n

lt-to-not-le : Set
lt-to-not-le =
  (n m : Nat) ->
  n < m ->
  Not (m <= n)
