-- Statement-only formalization of Logipedia corpus artifact nat.eq_minus_O
-- (catalog title "nat.eq_minus_O"): subtracting a greater or equal natural
-- number from a natural number yields zero. This file contains no proof.

{-# OPTIONS --safe #-}

module eq_minus_O where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _-_)

infix 4 _<=_

data _<=_ : Nat -> Nat -> Set where
  zero<=   : {n : Nat} -> zero <= n
  suc<=suc : {m n : Nat} -> m <= n -> suc m <= suc n

eq-minus-O : Set
eq-minus-O =
  (n m : Nat) ->
  n <= m ->
  n - m ≡ zero
