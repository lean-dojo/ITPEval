-- Statement-only formalization of Logipedia corpus artifact nat.not_le_Sn_n
-- (catalog title "nat.not_le_Sn_n"): no successor natural number is less than
-- or equal to the natural number it succeeds. This file contains no proof.

{-# OPTIONS --safe #-}

module not_le_Sn_n where

open import Agda.Builtin.Nat using (Nat; zero; suc)

infix 4 _<=_

data Bottom : Set where

Not : Set -> Set
Not A =
  A -> Bottom

data _<=_ : Nat -> Nat -> Set where
  zero<=   : {n : Nat} -> zero <= n
  suc<=suc : {m n : Nat} -> m <= n -> suc m <= suc n

nat-not-le-Sn-n : Set
nat-not-le-Sn-n =
  (n : Nat) ->
  Not (suc n <= n)
