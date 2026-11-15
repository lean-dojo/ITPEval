-- Statement-only formalization of Logipedia corpus artifact nat.match_nat_prop:
-- the natural-number case-exhaustion principle that a predicate holding at
-- zero and at every successor holds for every natural. This file contains no
-- proof.

{-# OPTIONS --safe #-}

module match_nat_prop where

open import Agda.Builtin.Nat using (Nat; zero; suc)

match-nat-prop : Set₁
match-nat-prop =
  (return : Nat → Set) →
  return zero →
  ((n : Nat) → return (suc n)) →
  (z : Nat) →
  return z
