-- Statement-only formalization of Logipedia corpus artifact nat.leb_elim
-- (catalog title "nat.leb_elim"): Boolean natural-number less-than-or-equal
-- comparison eliminates into the order and non-order branches. This file
-- contains no proof.

{-# OPTIONS --safe #-}

module leb_elim where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Nat using (Nat; zero; suc)

infix 4 _<=_

data Bottom : Set where

Not : Set -> Set
Not A =
  A -> Bottom

data _<=_ : Nat -> Nat -> Set where
  zero<=   : {n : Nat} -> zero <= n
  suc<=suc : {m n : Nat} -> m <= n -> suc m <= suc n

leb : Nat -> Nat -> Bool
leb zero n = true
leb (suc m) zero = false
leb (suc m) (suc n) = leb m n

leb-elim : Set₁
leb-elim =
  (n m : Nat) ->
  (P : Bool -> Set) ->
  (n <= m -> P true) ->
  (Not (n <= m) -> P false) ->
  P (leb n m)
