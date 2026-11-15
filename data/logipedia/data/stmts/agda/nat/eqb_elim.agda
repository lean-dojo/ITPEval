-- Statement-only formalization of Logipedia corpus artifact nat.eqb_elim
-- (catalog title "nat.eqb_elim"): Boolean equality on natural numbers
-- eliminates into the equality and inequality branches. This file contains no proof.

{-# OPTIONS --safe #-}

module eqb_elim where

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

eqb-elim : Set₁
eqb-elim =
  (n m : Nat) ->
  (P : Bool -> Set) ->
  (n ≡ m -> P true) ->
  (Not (n ≡ m) -> P false) ->
  P (eqb n m)
