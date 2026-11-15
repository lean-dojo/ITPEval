-- Statement-only formalization of Logipedia corpus artifact nat.commutative_times
-- (catalog title "nat.commutative_times"): multiplication on the natural
-- numbers is commutative. This file contains no proof.

{-# OPTIONS --safe #-}

module commutative_times where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat; _*_)

commutative-times : Set
commutative-times =
  (x y : Nat) ->
  x * y ≡ y * x
