-- Statement-only formalization of Logipedia corpus artifact nat.leb_true_to_le
-- (catalog title "nat.leb_true_to_le"): if Boolean natural-number
-- less-than-or-equal returns true, then the corresponding order holds. This
-- file contains no proof.

{-# OPTIONS --safe #-}

module leb_true_to_le where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat; zero; suc)

infix 4 _<=_

data _<=_ : Nat -> Nat -> Set where
  zero<=   : {n : Nat} -> zero <= n
  suc<=suc : {m n : Nat} -> m <= n -> suc m <= suc n

leb : Nat -> Nat -> Bool
leb zero n = true
leb (suc m) zero = false
leb (suc m) (suc n) = leb m n

leb-true-to-le : Set
leb-true-to-le =
  (n m : Nat) ->
  leb n m ≡ true ->
  n <= m
