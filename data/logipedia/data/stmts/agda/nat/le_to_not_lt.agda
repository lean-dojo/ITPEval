-- Statement-only formalization of Logipedia corpus artifact nat.le_to_not_lt
-- (catalog title "nat.le_to_not_lt"): a natural-number inequality n <= m
-- excludes the reverse strict inequality m < n. This file contains no proof.

{-# OPTIONS --safe #-}

module le_to_not_lt where

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

le-to-not-lt : Set
le-to-not-lt =
  (n m : Nat) ->
  n <= m ->
  Not (m < n)
