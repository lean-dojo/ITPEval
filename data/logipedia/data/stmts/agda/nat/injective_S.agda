-- Statement-only formalization of Logipedia corpus artifact nat.injective_S
-- (catalog title "nat.injective_S"): successor is injective on the natural
-- numbers. This file contains no proof.

{-# OPTIONS --safe #-}

module injective_S where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat; suc)

injective-S : Set
injective-S =
  (m n : Nat) ->
  suc m ≡ suc n ->
  m ≡ n
