-- Statement-only formalization of Logipedia corpus artifact nat.minus_minus
-- (catalog title "nat.minus_minus"): for natural numbers p at most m at most
-- n, adding p to the difference n minus m equals n minus the difference m
-- minus p. This file contains no proof.

{-# OPTIONS --safe #-}

module minus_minus where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _-_)

infix 4 _<=_

data _<=_ : Nat -> Nat -> Set where
  zero<=   : {n : Nat} -> zero <= n
  suc<=suc : {m n : Nat} -> m <= n -> suc m <= suc n

minus-minus : Set
minus-minus =
  (n m p : Nat) ->
  p <= m ->
  m <= n ->
  p + (n - m) ≡ n - (m - p)
