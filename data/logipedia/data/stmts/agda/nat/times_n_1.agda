-- Statement-only formalization of Logipedia corpus artifact nat.times_n_1
-- (catalog title "nat.times_n_1"): multiplying any natural number by one on
-- the right leaves it unchanged. This file contains no proof.

{-# OPTIONS --safe #-}

module TimesN1 where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _*_)

times-n-1 : Set
times-n-1 =
  (n : Nat) ->
  n ≡ n * suc zero
