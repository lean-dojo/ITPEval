-- Statement-only formalization of Logipedia corpus artifact nat.le_O_n
-- (catalog title "nat.le_O_n"): zero is less than or equal to every natural
-- number. This file contains no proof.

{-# OPTIONS --safe #-}

module le_O_n where

open import Agda.Builtin.Nat using (Nat; zero; suc)

infix 4 _<=_

data _<=_ : Nat -> Nat -> Set where
  zero<=   : {n : Nat} -> zero <= n
  suc<=suc : {m n : Nat} -> m <= n -> suc m <= suc n

le-O-n : Set
le-O-n =
  (n : Nat) ->
  zero <= n
