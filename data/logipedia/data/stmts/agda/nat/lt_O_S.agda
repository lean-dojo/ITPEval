-- Statement-only formalization of Logipedia corpus artifact nat.lt_O_S
-- (catalog title "nat.lt_O_S"): zero is strictly less than the successor of
-- every natural number. This file contains no proof.

{-# OPTIONS --safe #-}

module lt_O_S where

open import Agda.Builtin.Nat using (Nat; zero; suc)

infix 4 _<=_ _<_

data _<=_ : Nat -> Nat -> Set where
  zero<=   : {n : Nat} -> zero <= n
  suc<=suc : {m n : Nat} -> m <= n -> suc m <= suc n

_<_ : Nat -> Nat -> Set
m < n =
  suc m <= n

lt-O-S : Set
lt-O-S =
  (n : Nat) ->
  zero < suc n
