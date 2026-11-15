-- Statement-only formalization of Logipedia corpus artifact nat.plus_minus
-- (catalog title "nat.plus_minus"): if one natural number is at most another,
-- then adding after truncated subtraction equals subtracting after addition.
-- This file contains no proof.

{-# OPTIONS --safe #-}

module plus_minus where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _-_)

infix 4 _<=_

data _<=_ : Nat -> Nat -> Set where
  zero<=   : {n : Nat} -> zero <= n
  suc<=suc : {m n : Nat} -> m <= n -> suc m <= suc n

plus-minus : Set
plus-minus =
  (m n p : Nat) ->
  m <= n ->
  (n - m) + p ≡ (n + p) - m
