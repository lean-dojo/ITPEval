-- Statement-only formalization of Logipedia corpus artifact nat.minus_le
-- (catalog title "nat.minus_le"): truncated subtraction of natural numbers
-- never exceeds the minuend. This file contains no proof.

{-# OPTIONS --safe #-}

module minus_le where

open import Agda.Builtin.Nat using (Nat; zero; suc; _-_)

infix 4 _<=_

data _<=_ : Nat -> Nat -> Set where
  zero<=   : {n : Nat} -> zero <= n
  suc<=suc : {m n : Nat} -> m <= n -> suc m <= suc n

minus-le : Set
minus-le =
  (x y : Nat) ->
  (x - y) <= x
