-- Statement-only formalization of Logipedia corpus artifact nat.ltn_to_ltO
-- (catalog title "nat.ltn_to_ltO"): if one natural number is strictly less
-- than another, then zero is strictly less than the latter. This file
-- contains no proof.

{-# OPTIONS --safe #-}

module ltn_to_ltO where

open import Agda.Builtin.Nat using (Nat; zero; suc)

infix 4 _<=_ _<_

data _<=_ : Nat -> Nat -> Set where
  zero<=   : {n : Nat} -> zero <= n
  suc<=suc : {m n : Nat} -> m <= n -> suc m <= suc n

_<_ : Nat -> Nat -> Set
m < n =
  suc m <= n

ltn-to-ltO : Set
ltn-to-ltO =
  (n m : Nat) ->
  n < m ->
  zero < m
