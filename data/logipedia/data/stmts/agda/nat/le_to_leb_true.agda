-- Statement-only formalization of Logipedia corpus artifact nat.le_to_leb_true
-- (catalog title "nat.le_to_leb_true"): natural-number less-than-or-equal
-- implies that the corresponding Boolean comparison returns true. This file
-- contains no proof.

{-# OPTIONS --safe #-}

module le_to_leb_true where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat; zero; suc)

infix 4 _<=_

data _<=_ : Nat -> Nat -> Set where
  zero<=   : {n : Nat} -> zero <= n
  suc<=suc : {m n : Nat} -> m <= n -> suc m <= suc n

leb : Nat -> Nat -> Bool
leb zero n = true
leb (suc m) zero = false
leb (suc m) (suc n) = leb m n

le-to-leb-true : Set
le-to-leb-true =
  (n m : Nat) ->
  n <= m ->
  leb n m ≡ true
