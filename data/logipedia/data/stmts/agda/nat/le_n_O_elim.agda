-- Statement-only formalization of Logipedia corpus artifact nat.le_n_O_elim
-- (catalog title "nat.le_n_O_elim"): a natural number at most zero satisfies
-- every predicate that holds at zero. This file contains no proof.

{-# OPTIONS --safe #-}

module le_n_O_elim where

open import Agda.Builtin.Nat using (Nat; zero; suc)

infix 4 _<=_

data _<=_ : Nat -> Nat -> Set where
  zero<=   : {n : Nat} -> zero <= n
  suc<=suc : {m n : Nat} -> m <= n -> suc m <= suc n

nat-le-n-O-elim : Set₁
nat-le-n-O-elim =
  (n : Nat) ->
  n <= zero ->
  (P : Nat -> Set) ->
  P zero ->
  P n
