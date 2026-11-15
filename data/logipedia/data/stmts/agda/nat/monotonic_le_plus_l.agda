-- Statement-only formalization of Logipedia corpus artifact
-- nat.monotonic_le_plus_l (catalog title "nat.monotonic_le_plus_l"):
-- adding a fixed natural number on the right is monotone for the natural
-- number order. This file contains no proof.

{-# OPTIONS --safe #-}

module monotonic_le_plus_l where

open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)

infix 4 _<=_

data _<=_ : Nat -> Nat -> Set where
  zero<=   : {n : Nat} -> zero <= n
  suc<=suc : {m n : Nat} -> m <= n -> suc m <= suc n

monotonic-le-plus-l : Set
monotonic-le-plus-l =
  (m x y : Nat) ->
  x <= y ->
  (x + m) <= (y + m)
