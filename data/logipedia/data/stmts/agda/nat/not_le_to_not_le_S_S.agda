-- Statement-only formalization of Logipedia corpus artifact nat.not_le_to_not_le_S_S
-- (catalog title "nat.not_le_to_not_le_S_S"): failure of the natural-number
-- order is preserved when successor is applied to both sides. This file
-- contains no proof.

{-# OPTIONS --safe #-}

module not_le_to_not_le_S_S where

open import Agda.Builtin.Nat using (Nat; zero; suc)

infix 4 _<=_

data Bottom : Set where

Not : Set -> Set
Not A =
  A -> Bottom

data _<=_ : Nat -> Nat -> Set where
  zero<=   : {n : Nat} -> zero <= n
  suc<=suc : {m n : Nat} -> m <= n -> suc m <= suc n

nat-not-le-to-not-le-S-S : Set
nat-not-le-to-not-le-S-S =
  (n m : Nat) ->
  Not (n <= m) ->
  Not (suc n <= suc m)
