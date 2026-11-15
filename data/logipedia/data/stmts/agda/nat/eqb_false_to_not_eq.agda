-- Statement-only formalization of Logipedia corpus artifact nat.eqb_false_to_not_eq
-- (catalog title "nat.eqb_false_to_not_eq"): if Boolean equality of two natural
-- numbers is false, then the natural numbers are unequal. This file contains no proof.

{-# OPTIONS --safe #-}

module eqb_false_to_not_eq where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat; zero; suc)

data Bottom : Set where

Not : Set -> Set
Not A =
  A -> Bottom

eqb : Nat -> Nat -> Bool
eqb zero zero = true
eqb zero (suc n) = false
eqb (suc m) zero = false
eqb (suc m) (suc n) = eqb m n

eqb-false-to-not-eq : Set
eqb-false-to-not-eq =
  (n m : Nat) ->
  eqb n m ≡ false ->
  Not (n ≡ m)
