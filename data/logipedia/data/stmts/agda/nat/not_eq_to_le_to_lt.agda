-- Statement-only formalization of Logipedia corpus artifact nat.not_eq_to_le_to_lt
-- (catalog title "nat.not_eq_to_le_to_lt"): for natural numbers n and m,
-- n not equal to m and n <= m imply n < m. This file contains no proof.

{-# OPTIONS --safe #-}

module not_eq_to_le_to_lt where

open import Agda.Builtin.Equality using (_≡_)
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

not-eq-to-le-to-lt : Set
not-eq-to-le-to-lt =
  (n m : Nat) ->
  Not (n ≡ m) ->
  n <= m ->
  n < m
