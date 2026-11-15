-- Statement-only formalization of Logipedia corpus artifact nat.lt_to_not_zero
-- (catalog title "nat.lt_to_not_zero"): a strict natural-number inequality
-- n < m implies that m is nonzero. This file contains no proof.

{-# OPTIONS --safe #-}

module lt_to_not_zero where

open import Agda.Builtin.Nat using (Nat; zero; suc)

infix 4 _<=_ _<_

data Bottom : Set where

data Top : Set where
  top : Top

data _<=_ : Nat -> Nat -> Set where
  zero<=   : {n : Nat} -> zero <= n
  suc<=suc : {m n : Nat} -> m <= n -> suc m <= suc n

_<_ : Nat -> Nat -> Set
m < n =
  suc m <= n

NotZero : Nat -> Set
NotZero zero =
  Bottom
NotZero (suc n) =
  Top

lt-to-not-zero : Set
lt-to-not-zero =
  (n m : Nat) ->
  n < m ->
  NotZero m
