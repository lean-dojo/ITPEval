-- Statement-only formalization of miniF2F test problem mathd_numbertheory_353. This file
-- contains no proof.

module mathd-numbertheory-353 where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using
  (Nat; zero; suc; _+_; mod-helper)

sumFrom : Nat → Nat → Nat
sumFrom start zero = zero
sumFrom start (suc count) = start + sumFrom (suc start) count

naturalMod : Nat → Nat → Nat
naturalMod numerator zero = zero
naturalMod numerator (suc denominator) =
  mod-helper zero denominator numerator denominator

mathd-numbertheory-353 : Set
mathd-numbertheory-353 =
  (s : Nat) →
  s ≡ sumFrom 2010 2009 →
  naturalMod s 2009 ≡ zero
