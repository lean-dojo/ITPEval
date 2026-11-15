-- Statement-only formalization of Logipedia corpus artifact nat.le_n_O_to_eq
-- (catalog title "nat.le_n_O_to_eq"): a natural number less than or equal to
-- zero is equal to zero. This file contains no proof.

{-# OPTIONS --safe #-}

module le_n_O_to_eq where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat; zero; suc)

infix 4 _<=_

data _<=_ : Nat -> Nat -> Set where
  zero<=   : {n : Nat} -> zero <= n
  suc<=suc : {m n : Nat} -> m <= n -> suc m <= suc n

nat-le-n-O-to-eq : Set
nat-le-n-O-to-eq =
  (n : Nat) ->
  n <= zero ->
  zero ≡ n
