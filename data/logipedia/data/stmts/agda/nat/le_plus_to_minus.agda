-- Statement-only formalization of Logipedia corpus artifact
-- nat.le_plus_to_minus (catalog title "nat.le_plus_to_minus"): if a natural
-- number is at most p plus m, then its truncated difference with m is at most
-- p. This file contains no proof.

{-# OPTIONS --safe #-}

module le_plus_to_minus where

open import Agda.Builtin.Nat using (Nat; suc; _+_; _-_)

infix 4 _<=_

data _<=_ : Nat -> Nat -> Set where
  le-refl : {n : Nat} -> n <= n
  le-step : {n m : Nat} -> n <= m -> n <= suc m

le-plus-to-minus : Set
le-plus-to-minus =
  (n m p : Nat) ->
  n <= (p + m) ->
  (n - m) <= p
