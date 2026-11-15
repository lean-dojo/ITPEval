-- Statement-only formalization of Logipedia corpus artifact nat.nat_ind
-- (catalog title "nat.nat_ind"): mathematical induction for predicates on
-- natural numbers from the zero case and successor step. This file contains no proof.

{-# OPTIONS --safe #-}

module nat_ind where

open import Agda.Builtin.Nat using (Nat; zero; suc)

nat-ind : Set₁
nat-ind =
  (Q : Nat -> Set) ->
  Q zero ->
  ((x : Nat) -> Q x -> Q (suc x)) ->
  (x : Nat) ->
  Q x
