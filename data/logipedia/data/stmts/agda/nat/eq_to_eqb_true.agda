-- Statement-only formalization of Logipedia corpus artifact nat.eq_to_eqb_true
-- (catalog title "nat.eq_to_eqb_true"): equality of two natural numbers implies
-- that their Boolean equality test returns true. This file contains no proof.

{-# OPTIONS --safe #-}

module eq_to_eqb_true where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat; zero; suc)

eqb : Nat -> Nat -> Bool
eqb zero zero = true
eqb zero (suc n) = false
eqb (suc m) zero = false
eqb (suc m) (suc n) = eqb m n

eq-to-eqb-true : Set
eq-to-eqb-true =
  (n m : Nat) ->
  n ≡ m ->
  eqb n m ≡ true
