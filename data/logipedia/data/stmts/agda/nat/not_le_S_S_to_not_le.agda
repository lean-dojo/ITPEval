-- Statement-only formalization of Logipedia corpus artifact nat.not_le_S_S_to_not_le
-- (catalog title "nat.not_le_S_S_to_not_le"): failure of the natural-number
-- order after applying successor implies failure before successor. This file
-- contains no proof.

{-# OPTIONS --safe #-}

module not_le_S_S_to_not_le where

open import Agda.Builtin.Nat using (Nat; zero; suc)

infix 4 _<=_

data Bottom : Set where

Not : Set -> Set
Not A =
  A -> Bottom

data _<=_ : Nat -> Nat -> Set where
  zero<=   : {n : Nat} -> zero <= n
  suc<=suc : {m n : Nat} -> m <= n -> suc m <= suc n

nat-not-le-S-S-to-not-le : Set
nat-not-le-S-S-to-not-le =
  (n m : Nat) ->
  Not (suc n <= suc m) ->
  Not (n <= m)
