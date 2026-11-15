-- Statement-only formalization of Logipedia corpus artifact exp.lt_O_exp
-- (catalog title "exp.lt_O_exp"): every positive natural base has a positive
-- value at every natural exponent. This file contains no proof.

{-# OPTIONS --safe #-}

module lt_O_exp where

open import Agda.Builtin.Nat using (Nat; zero; suc; _*_)

infix 4 _<_

data _<_ : Nat -> Nat -> Set where
  zero<suc : {n : Nat} -> zero < suc n
  suc<suc : {m n : Nat} -> m < n -> suc m < suc n

exp : Nat -> Nat -> Nat
exp n zero = suc zero
exp n (suc m) = (exp n m) * n

lt-O-exp : Set
lt-O-exp =
  (n m : Nat) ->
  zero < n ->
  zero < exp n m
