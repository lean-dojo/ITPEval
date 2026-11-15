-- Statement-only formalization of Logipedia corpus artifact nat.assoc_plus1
-- (catalog title "nat.assoc_plus1"): for all natural numbers a, b, and c,
-- c + (b + a) equals (b + c) + a. This file contains no proof.

{-# OPTIONS --safe #-}

module assoc_plus1 where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat; _+_)

assoc-plus1 : Set
assoc-plus1 =
  (a b c : Nat) ->
  c + (b + a) ≡ (b + c) + a
