-- Statement-only formalization of Logipedia corpus artifact nat.lt_to_le
-- (catalog title "nat.lt_to_le"): every strict natural-number inequality
-- implies the corresponding non-strict inequality. This file contains no proof.

{-# OPTIONS --safe #-}

module lt_to_le where

open import Agda.Builtin.Nat using (Nat; zero; suc)

infix 4 _<=_ _<_

data _<=_ : Nat -> Nat -> Set where
  zero<=   : {n : Nat} -> zero <= n
  suc<=suc : {m n : Nat} -> m <= n -> suc m <= suc n

_<_ : Nat -> Nat -> Set
m < n =
  suc m <= n

nat-lt-to-le : Set
nat-lt-to-le =
  (x y : Nat) ->
  x < y ->
  x <= y
