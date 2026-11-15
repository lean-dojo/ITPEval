-- Statement-only formalization of Logipedia corpus artifact nat.le_pred_n
-- (catalog title "nat.le_pred_n"): the predecessor of every natural number is
-- less than or equal to that number. This file contains no proof.

{-# OPTIONS --safe #-}

module le_pred_n where

open import Agda.Builtin.Nat using (Nat; zero; suc)

infix 4 _<=_

data _<=_ : Nat -> Nat -> Set where
  zero<=   : {n : Nat} -> zero <= n
  suc<=suc : {m n : Nat} -> m <= n -> suc m <= suc n

pred : Nat -> Nat
pred zero = zero
pred (suc n) = n

le-pred-n : Set
le-pred-n =
  (n : Nat) ->
  pred n <= n
