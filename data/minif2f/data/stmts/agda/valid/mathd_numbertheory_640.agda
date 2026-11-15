-- Statement-only formalization of miniF2F valid problem mathd_numbertheory_640. This file
-- contains no proof.

module mathd-numbertheory-640 where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; mod-helper)

naturalMod : Nat → Nat → Nat
naturalMod numerator zero = zero
naturalMod numerator (suc denominator) =
  mod-helper zero denominator numerator denominator

mathd-numbertheory-640 : Set
mathd-numbertheory-640 =
  naturalMod (91145 + 91146 + 91147 + 91148) 4 ≡ 2
