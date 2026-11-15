-- Statement-only formalization of Logipedia corpus artifact nat.lt_S_to_lt
-- (catalog title "nat.lt_S_to_lt"): if the successor of a natural number is
-- strictly less than another, then the original number is too. This file
-- contains no proof.

{-# OPTIONS --safe #-}

module lt_S_to_lt where

open import Agda.Builtin.Nat using (Nat; zero; suc)

infix 4 _<=_ _<_

data _<=_ : Nat -> Nat -> Set where
  zero<=   : {n : Nat} -> zero <= n
  suc<=suc : {m n : Nat} -> m <= n -> suc m <= suc n

_<_ : Nat -> Nat -> Set
m < n =
  suc m <= n

lt-S-to-lt : Set
lt-S-to-lt =
  (n m : Nat) ->
  suc n < m ->
  n < m
