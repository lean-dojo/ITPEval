-- Statement-only formalization of miniF2F valid problem mathd_numbertheory_45. This file
-- contains no proof.

module mathd-numbertheory-45 where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using
  (Nat; zero; suc; _+_; mod-helper)

naturalMod : Nat → Nat → Nat
naturalMod numerator zero = zero
naturalMod numerator (suc denominator) =
  mod-helper zero denominator numerator denominator

gcdWithFuel : Nat → Nat → Nat → Nat
gcdWithFuel zero a b = a
gcdWithFuel (suc fuel) a zero = a
gcdWithFuel (suc fuel) a (suc b) =
  gcdWithFuel fuel (suc b) (naturalMod a (suc b))

naturalGCD : Nat → Nat → Nat
naturalGCD a b =
  gcdWithFuel (suc (a + b)) a b

mathd-numbertheory-45 : Set
mathd-numbertheory-45 =
  naturalGCD 6432 132 + 11 ≡ 23
