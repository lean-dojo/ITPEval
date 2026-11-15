-- Statement-only formalization of Logipedia corpus artifact
-- nat.minus_le_minus_minus_comm (catalog title
-- "nat.minus_le_minus_minus_comm"): for natural numbers c at most b,
-- subtracting b minus c from a equals subtracting b from a plus c. This file
-- contains no proof.

{-# OPTIONS --safe #-}

module minus_le_minus_minus_comm where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _-_)

infix 4 _<=_

data _<=_ : Nat -> Nat -> Set where
  zero<=   : {n : Nat} -> zero <= n
  suc<=suc : {m n : Nat} -> m <= n -> suc m <= suc n

minus-le-minus-minus-comm : Set
minus-le-minus-minus-comm =
  (b c a : Nat) ->
  c <= b ->
  a - (b - c) ≡ (a + c) - b
