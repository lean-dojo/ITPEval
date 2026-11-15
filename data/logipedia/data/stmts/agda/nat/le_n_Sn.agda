-- Statement-only formalization of Logipedia corpus artifact nat.le_n_Sn
-- (catalog title "nat.le_n_Sn"): every natural number is less than or equal
-- to its successor. This file contains no proof.

{-# OPTIONS --safe #-}

module le_n_Sn where

open import Agda.Builtin.Nat using (Nat; zero; suc)

infix 4 _<=_

data _<=_ : Nat -> Nat -> Set where
  zero<=   : {n : Nat} -> zero <= n
  suc<=suc : {m n : Nat} -> m <= n -> suc m <= suc n

le-n-Sn : Set
le-n-Sn =
  (n : Nat) ->
  n <= suc n
