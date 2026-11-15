-- Statement-only formalization of Logipedia corpus artifact
-- nat.monotonic_le_minus_l (catalog title "nat.monotonic_le_minus_l"):
-- natural-number truncated subtraction is monotone in its left operand. This
-- file contains no proof.

{-# OPTIONS --safe #-}

module monotonic_le_minus_l where

open import Agda.Builtin.Nat using (Nat; zero; suc; _-_)

infix 4 _<=_

data _<=_ : Nat -> Nat -> Set where
  zero<=   : {n : Nat} -> zero <= n
  suc<=suc : {m n : Nat} -> m <= n -> suc m <= suc n

monotonic-le-minus-l : Set
monotonic-le-minus-l =
  (p q n : Nat) ->
  q <= p ->
  (q - n) <= (p - n)
