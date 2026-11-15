-- Statement-only formalization of Logipedia corpus artifact
-- nat.monotonic_lt_times_l (catalog title "nat.monotonic_lt_times_l"):
-- multiplication by a fixed positive natural number on the right preserves
-- strict order on the natural numbers. This file contains no proof.

{-# OPTIONS --safe #-}

module monotonic_lt_times_l where

open import Agda.Builtin.Nat using (Nat; zero; suc; _*_)

infix 4 _<=_ _<_

data _<=_ : Nat -> Nat -> Set where
  le-refl : {n : Nat} -> n <= n
  le-step : {n m : Nat} -> n <= m -> n <= suc m

_<_ : Nat -> Nat -> Set
m < n =
  suc m <= n

Monotonic : (Nat -> Nat -> Set) -> (Nat -> Nat) -> Set
Monotonic R f =
  (x y : Nat) -> R x y -> R (f x) (f y)

monotonic-lt-times-l : Set
monotonic-lt-times-l =
  (c : Nat) ->
  zero < c ->
  Monotonic _<_ (\ t -> t * c)
