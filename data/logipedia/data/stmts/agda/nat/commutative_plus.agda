-- Statement-only formalization of Logipedia corpus artifact nat.commutative_plus
-- (catalog title "nat.commutative_plus"): addition on the natural numbers is
-- commutative. This file contains no proof.

{-# OPTIONS --safe #-}

module commutative_plus where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat; _+_)

commutative-plus : Set
commutative-plus =
  (x y : Nat) ->
  x + y ≡ y + x
