-- Statement-only formalization of Logipedia corpus artifact
-- nat.monotonic_le_plus_r (catalog title "nat.monotonic_le_plus_r"):
-- adding a fixed natural number on the left is monotone for the natural
-- number order. This file contains no proof.

{-# OPTIONS --safe #-}

module monotonic_le_plus_r where

open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)

infix 4 _<=_

data _<=_ : Nat -> Nat -> Set where
  zero<=   : {n : Nat} -> zero <= n
  suc<=suc : {m n : Nat} -> m <= n -> suc m <= suc n

monotonic-le-plus-r : Set
monotonic-le-plus-r =
  (n x y : Nat) ->
  x <= y ->
  (n + x) <= (n + y)
