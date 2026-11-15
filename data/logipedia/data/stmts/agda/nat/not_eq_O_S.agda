-- Statement-only formalization of Logipedia corpus artifact nat.not_eq_O_S
-- (catalog title "nat.not_eq_O_S"): zero is not equal to the successor of
-- any natural number. This file contains no proof.

{-# OPTIONS --safe #-}

module not_eq_O_S where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat; zero; suc)

data Bottom : Set where

Not : Set -> Set
Not A =
  A -> Bottom

not-eq-O-S : Set
not-eq-O-S =
  (n : Nat) ->
  Not (zero ≡ suc n)
