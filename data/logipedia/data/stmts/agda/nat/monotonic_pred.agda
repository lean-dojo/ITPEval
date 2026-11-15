-- Statement-only formalization of Logipedia corpus artifact nat.monotonic_pred
-- (catalog title "nat.monotonic_pred"): predecessor is monotone with respect
-- to the natural-number order. This file contains no proof.

{-# OPTIONS --safe #-}

module monotonic_pred where

open import Agda.Builtin.Nat using (Nat; zero; suc)

infix 4 _<=_

data _<=_ : Nat -> Nat -> Set where
  zero<=   : {n : Nat} -> zero <= n
  suc<=suc : {m n : Nat} -> m <= n -> suc m <= suc n

pred : Nat -> Nat
pred zero = zero
pred (suc n) = n

Monotonic : (Nat -> Nat -> Set) -> (Nat -> Nat) -> Set
Monotonic R f =
  (x y : Nat) -> R x y -> R (f x) (f y)

monotonic-pred : Set
monotonic-pred =
  Monotonic _<=_ pred
