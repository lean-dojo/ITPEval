-- Statement-only formalization of Logipedia corpus artifact nat.eqb_n_n,
-- catalog title "nat.eqb_n_n": Boolean equality on every natural number
-- returns true when the number is compared with itself. This file contains no proof.

module eqb_n_n where

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat; zero; suc)

eqb : Nat → Nat → Bool
eqb zero zero = true
eqb zero (suc m) = false
eqb (suc n) zero = false
eqb (suc n) (suc m) = eqb n m

nat-eqb-n-n : Set
nat-eqb-n-n = (n : Nat) → eqb n n ≡ true
