-- Statement-only formalization of Logipedia corpus artifact
-- div_mod.le_mod_aux_m_m (catalog title "div_mod.le_mod_aux_m_m"): if a
-- natural input is at most the recursion fuel, the fuel-bounded auxiliary
-- remainder is at most the given natural bound. This file contains no proof.

{-# OPTIONS --safe #-}

module le_mod_aux_m_m where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Nat using (Nat; zero; suc; _-_)

infix 4 _≤_

data _≤_ : Nat -> Nat -> Set where
  zero≤ : {n : Nat} -> zero ≤ n
  suc≤suc : {m n : Nat} -> m ≤ n -> suc m ≤ suc n

leb : Nat -> Nat -> Bool
leb zero n = true
leb (suc m) zero = false
leb (suc m) (suc n) = leb m n

mod-aux : Nat -> Nat -> Nat -> Nat
mod-aux zero n m = n
mod-aux (suc p) n m with leb n m
... | true = n
... | false = mod-aux p (n - suc m) m

le-mod-aux-m-m : Set
le-mod-aux-m-m =
  (p n m : Nat) ->
  n ≤ p ->
  mod-aux p n m ≤ m
