-- Statement-only formalization of Logipedia corpus artifact nat.not_eq_S
-- (catalog title "nat.not_eq_S"): applying successor to two unequal natural
-- numbers yields unequal successors. This file contains no proof.

{-# OPTIONS --safe #-}

module not_eq_S where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat; suc)

data Bottom : Set where

Not : Set -> Set
Not A =
  A -> Bottom

not-eq-S : Set
not-eq-S =
  (n m : Nat) ->
  Not (n ≡ m) ->
  Not (suc n ≡ suc m)
