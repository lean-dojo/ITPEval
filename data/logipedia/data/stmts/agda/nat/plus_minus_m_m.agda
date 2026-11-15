-- Statement-only formalization of Logipedia corpus artifact nat.plus_minus_m_m
-- (catalog title "nat.plus_minus_m_m"): if a natural number m is at most n,
-- adding m to the truncated difference n minus m recovers n. This file
-- contains no proof.

{-# OPTIONS --safe #-}

module plus_minus_m_m where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _-_)

infix 4 _<=_

data _<=_ : Nat -> Nat -> Set where
  zero<=   : {n : Nat} -> zero <= n
  suc<=suc : {m n : Nat} -> m <= n -> suc m <= suc n

plus-minus-m-m : Set
plus-minus-m-m =
  (n m : Nat) ->
  m <= n ->
  n ≡ (n - m) + m
