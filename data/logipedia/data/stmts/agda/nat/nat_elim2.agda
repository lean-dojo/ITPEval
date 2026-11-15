-- Statement-only formalization of Logipedia corpus artifact nat.nat_elim2
-- (catalog title "nat.nat_elim2"): two-dimensional induction on pairs of
-- natural numbers from the zero row, positive zero column, and simultaneous
-- successor step. This file contains no proof.

{-# OPTIONS --safe #-}

module nat_elim2 where

open import Agda.Builtin.Nat using (Nat; zero; suc)

nat-elim2 : Set₁
nat-elim2 =
  (R : Nat -> Nat -> Set) ->
  ((n : Nat) -> R zero n) ->
  ((n : Nat) -> R (suc n) zero) ->
  ((n m : Nat) -> R n m -> R (suc n) (suc m)) ->
  (n m : Nat) ->
  R n m
