-- Statement-only formalization of Logipedia corpus artifact
-- nat.le_plus_minus_m_m (catalog title "nat.le_plus_minus_m_m"): every natural
-- number is at most its truncated difference with another natural number plus
-- that second number. This file contains no proof.

{-# OPTIONS --safe #-}

module le_plus_minus_m_m where

open import Agda.Builtin.Nat using (Nat; suc; _+_; _-_)

infix 4 _<=_

data _<=_ : Nat -> Nat -> Set where
  le-refl : {n : Nat} -> n <= n
  le-step : {n m : Nat} -> n <= m -> n <= suc m

le-plus-minus-m-m : Set
le-plus-minus-m-m =
  (n m : Nat) ->
  n <= (n - m) + m
