-- Statement-only formalization of Logipedia corpus artifact nat.transitive_lt
-- (catalog title "nat.transitive_lt"): strict less-than on natural numbers is
-- transitive. This file contains no proof.

{-# OPTIONS --safe #-}

module transitive_lt where

open import Agda.Builtin.Nat using (Nat; suc)

infix 4 _<=_ _<_

data _<=_ : Nat -> Nat -> Set where
  le-refl : {n : Nat} -> n <= n
  le-step : {n m : Nat} -> n <= m -> n <= suc m

_<_ : Nat -> Nat -> Set
m < n =
  suc m <= n

transitive-lt : Set
transitive-lt =
  (a b c : Nat) ->
  a < b ->
  b < c ->
  a < c
