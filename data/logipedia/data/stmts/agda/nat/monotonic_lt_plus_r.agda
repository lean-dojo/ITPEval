-- Statement-only formalization of Logipedia corpus artifact
-- nat.monotonic_lt_plus_r (catalog title "nat.monotonic_lt_plus_r"):
-- for every natural n, the function mapping m to n + m preserves strict
-- order on the natural numbers. This file contains no proof.

{-# OPTIONS --safe #-}

module monotonic_lt_plus_r where

open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)

infix 4 _<=_ _<_

data _<=_ : Nat -> Nat -> Set where
  zero<= : {n : Nat} -> zero <= n
  suc<=suc : {m n : Nat} -> m <= n -> suc m <= suc n

_<_ : Nat -> Nat -> Set
m < n = suc m <= n

Monotonic : (Nat -> Nat -> Set) -> (Nat -> Nat) -> Set
Monotonic R f =
  (x y : Nat) -> R x y -> R (f x) (f y)

monotonic-lt-plus-r : Set
monotonic-lt-plus-r =
  (n : Nat) -> Monotonic _<_ (\ m -> n + m)
