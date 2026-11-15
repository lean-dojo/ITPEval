-- Statement-only formalization of miniF2F test problem mathd_numbertheory_343:
-- the product of the first six positive odd natural numbers is 5 modulo 10.
-- This file contains no proof.

module mathd-numbertheory-343 where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using
  (Nat; zero; suc; _+_; _*_; mod-helper)

naturalMod : Nat → Nat → Nat
naturalMod numerator zero = zero
naturalMod numerator (suc denominator) =
  mod-helper zero denominator numerator denominator

oddProductBelow : Nat → Nat
oddProductBelow zero = 1
oddProductBelow (suc n) =
  oddProductBelow n * (2 * n + 1)

mathd-numbertheory-343 : Set
mathd-numbertheory-343 =
  naturalMod (oddProductBelow 6) 10 ≡ 5
