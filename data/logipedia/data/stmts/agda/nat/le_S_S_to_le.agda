-- Statement-only formalization of Logipedia corpus artifact nat.le_S_S_to_le,
-- catalog title "nat.le_S_S_to_le": cancellation of successor on both sides
-- of the natural-number order. This file contains no proof.

{-# OPTIONS --safe #-}

module le_S_S_to_le where

open import Agda.Builtin.Nat using (Nat; zero; suc)

infix 4 _≤_

data _≤_ : Nat → Nat → Set where
  zero≤ : {n : Nat} → zero ≤ n
  suc≤suc : {m n : Nat} → m ≤ n → suc m ≤ suc n

nat-le-S-S-to-le : Set
nat-le-S-S-to-le =
  (n m : Nat) →
  suc n ≤ suc m →
  n ≤ m
