-- Statement-only formalization of miniF2F test problem mathd_numbertheory_3:
-- the sum of the squares of the first nine positive integers has remainder 5 modulo 10.
-- This file contains no proof.

{-# OPTIONS --safe #-}

module mathd-numbertheory-3 where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using
  (Nat; zero; suc; _+_; _*_; mod-helper)

sumFirst : Nat → (Nat → Nat) → Nat
sumFirst zero term = zero
sumFirst (suc n) term = sumFirst n term + term n

naturalMod : Nat → Nat → Nat
naturalMod numerator zero = zero
naturalMod numerator (suc denominator) =
  mod-helper zero denominator numerator denominator

mathd-numbertheory-3 : Set
mathd-numbertheory-3 =
  naturalMod (sumFirst 9 (λ x → (x + 1) * (x + 1))) 10 ≡ 5
