-- Statement-only formalization of Logipedia corpus artifact nat.minus_to_plus
-- (catalog title "nat.minus_to_plus"): if subtracting a smaller natural
-- number from a larger one yields p, then the larger number is that smaller
-- number plus p. This file contains no proof.

{-# OPTIONS --safe #-}

module minus_to_plus where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _-_)

infix 4 _<=_

data _<=_ : Nat -> Nat -> Set where
  zero<=   : {n : Nat} -> zero <= n
  suc<=suc : {m n : Nat} -> m <= n -> suc m <= suc n

minus-to-plus : Set
minus-to-plus =
  (n m p : Nat) ->
  m <= n ->
  n - m ≡ p ->
  n ≡ m + p
