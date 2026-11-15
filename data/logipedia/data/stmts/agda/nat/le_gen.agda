-- Statement-only formalization of Logipedia corpus artifact nat.le_gen
-- (catalog title "nat.le_gen"): a predicate holding for every natural number
-- at most n holds in particular at n. This file contains no proof.

{-# OPTIONS --safe #-}

module le_gen where

open import Agda.Builtin.Nat using (Nat; zero; suc)

infix 4 _<=_

data _<=_ : Nat -> Nat -> Set where
  zero<=   : {n : Nat} -> zero <= n
  suc<=suc : {m n : Nat} -> m <= n -> suc m <= suc n

nat-le-gen : Set₁
nat-le-gen =
  (P : Nat -> Set) ->
  (n : Nat) ->
  ((i : Nat) -> i <= n -> P i) ->
  P n
