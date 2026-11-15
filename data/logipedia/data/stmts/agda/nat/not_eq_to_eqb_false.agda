-- Statement-only formalization of Logipedia corpus artifact nat.not_eq_to_eqb_false
-- (catalog title "nat.not_eq_to_eqb_false"): inequality of two natural numbers
-- implies that their Boolean equality test returns false. This file contains no proof.

{-# OPTIONS --safe #-}

module not_eq_to_eqb_false where

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

not-eq-to-eqb-false : Set
not-eq-to-eqb-false =
  (n m : Nat) ->
  Not (n ≡ m) ->
  eqb n m ≡ false
