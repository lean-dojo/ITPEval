-- Statement-only formalization of Logipedia corpus artifact nat.not_lt_to_le
-- (catalog title "nat.not_lt_to_le"): for natural numbers n and m, if n is
-- not strictly less than m, then m is less than or equal to n. This file
-- contains no proof.

{-# OPTIONS --safe #-}

module not_lt_to_le where

open import Agda.Builtin.Nat using (Nat; zero; suc)

infix 4 _<=_ _<_

data Bottom : Set where

Not : Set -> Set
Not A =
  A -> Bottom

data _<=_ : Nat -> Nat -> Set where
  zero<=   : {n : Nat} -> zero <= n
  suc<=suc : {m n : Nat} -> m <= n -> suc m <= suc n

_<_ : Nat -> Nat -> Set
m < n =
  suc m <= n

nat-not-lt-to-le : Set
nat-not-lt-to-le =
  (n m : Nat) ->
  Not (n < m) ->
  m <= n
