-- Statement-only formalization of Logipedia corpus artifact nat.lt_O_n_elim
-- (catalog title "nat.lt_O_n_elim"): a strictly positive natural number
-- satisfies every predicate that holds for every successor. This file contains
-- no proof.

{-# OPTIONS --safe #-}

module lt_O_n_elim where

open import Agda.Builtin.Nat using (Nat; zero; suc)

infix 4 _<=_ _<_

data _<=_ : Nat -> Nat -> Set where
  zero<=   : {n : Nat} -> zero <= n
  suc<=suc : {m n : Nat} -> m <= n -> suc m <= suc n

_<_ : Nat -> Nat -> Set
m < n =
  suc m <= n

nat-lt-O-n-elim : Set₁
nat-lt-O-n-elim =
  (n : Nat) ->
  zero < n ->
  (P : Nat -> Set) ->
  ((m : Nat) -> P (suc m)) ->
  P n
