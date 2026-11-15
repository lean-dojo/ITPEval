-- Statement-only formalization of Logipedia corpus artifact
-- nat.monotonic_le_minus_r (catalog title "nat.monotonic_le_minus_r"):
-- natural-number truncated subtraction is antitone in its right operand. This
-- file contains no proof.

{-# OPTIONS --safe #-}

module monotonic_le_minus_r where

open import Agda.Builtin.Nat using (Nat; zero; suc; _-_)

infix 4 _<=_

data _<=_ : Nat -> Nat -> Set where
  zero<=   : {n : Nat} -> zero <= n
  suc<=suc : {m n : Nat} -> m <= n -> suc m <= suc n

monotonic-le-minus-r : Set
monotonic-le-minus-r =
  (p q n : Nat) ->
  q <= p ->
  (n - p) <= (n - q)
