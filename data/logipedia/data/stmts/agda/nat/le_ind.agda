-- Statement-only formalization of Logipedia corpus artifact nat.le_ind
-- (catalog title "nat.le_ind"): induction over natural numbers from an
-- arbitrary lower bound with a successor step. This file contains no proof.

{-# OPTIONS --safe #-}

module le_ind where

open import Agda.Builtin.Nat using (Nat; zero; suc)

infix 4 _<=_

data _<=_ : Nat -> Nat -> Set where
  zero<=   : {n : Nat} -> zero <= n
  suc<=suc : {m n : Nat} -> m <= n -> suc m <= suc n

nat-le-ind : Set₁
nat-le-ind =
  (n : Nat) ->
  (Q : Nat -> Set) ->
  Q n ->
  ((m : Nat) -> n <= m -> Q m -> Q (suc m)) ->
  (m : Nat) ->
  n <= m ->
  Q m
