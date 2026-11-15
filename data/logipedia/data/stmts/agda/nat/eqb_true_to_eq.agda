-- Statement-only formalization of Logipedia corpus artifact nat.eqb_true_to_eq
-- (catalog title "nat.eqb_true_to_eq"): if the Boolean equality test on two
-- natural numbers returns true, then the numbers are equal. This file contains no proof.

{-# OPTIONS --safe #-}

module eqb_true_to_eq where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat; zero; suc)

eqb : Nat -> Nat -> Bool
eqb zero zero = true
eqb zero (suc n) = false
eqb (suc m) zero = false
eqb (suc m) (suc n) = eqb m n

eqb-true-to-eq : Set
eqb-true-to-eq =
  (n m : Nat) ->
  eqb n m ≡ true ->
  n ≡ m
