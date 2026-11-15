-- Statement-only formalization of miniF2F test problem mathd_numbertheory_345. This file
-- contains no proof.

module mathd-numbertheory-345 where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using
  (Nat; zero; suc; _+_; mod-helper)

naturalMod : Nat → Nat → Nat
naturalMod numerator zero = zero
naturalMod numerator (suc denominator) =
  mod-helper zero denominator numerator denominator

mathd-numbertheory-345 : Set
mathd-numbertheory-345 =
  naturalMod (2000 + 2001 + 2002 + 2003 + 2004 + 2005 + 2006) 7 ≡ zero
