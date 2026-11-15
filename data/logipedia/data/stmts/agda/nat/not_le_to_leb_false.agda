-- Statement-only formalization of Logipedia corpus artifact
-- nat.not_le_to_leb_false (catalog title "nat.not_le_to_leb_false"):
-- failure of natural-number less-than-or-equal implies that the corresponding
-- Boolean comparison returns false. This file contains no proof.

{-# OPTIONS --safe #-}

module not_le_to_leb_false where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat; zero; suc)

data Bottom : Set where

Not : Set -> Set
Not A =
  A -> Bottom

infix 4 _<=_

data _<=_ : Nat -> Nat -> Set where
  zero<=   : {n : Nat} -> zero <= n
  suc<=suc : {m n : Nat} -> m <= n -> suc m <= suc n

leb : Nat -> Nat -> Bool
leb zero n = true
leb (suc m) zero = false
leb (suc m) (suc n) = leb m n

not-le-to-leb-false : Set
not-le-to-leb-false =
  (n m : Nat) ->
  Not (n <= m) ->
  leb n m ≡ false
