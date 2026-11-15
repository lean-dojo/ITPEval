-- Statement-only formalization of Logipedia corpus artifact nat.S_pred
-- (catalog title "nat.S_pred"): every positive natural number is the
-- successor of its predecessor. This file contains no proof.

{-# OPTIONS --safe #-}

module S_pred where

open import Agda.Builtin.Equality renaming (_≡_ to _==_)
open import Agda.Builtin.Nat using (Nat; zero; suc)

infix 4 _<=_ _<_

data _<=_ : Nat -> Nat -> Set where
  zero<=   : {n : Nat} -> zero <= n
  suc<=suc : {m n : Nat} -> m <= n -> suc m <= suc n

_<_ : Nat -> Nat -> Set
m < n =
  suc m <= n

pred : Nat -> Nat
pred zero =
  zero
pred (suc n) =
  n

S-pred : Set
S-pred =
  (n : Nat) ->
  zero < n ->
  suc (pred n) == n
