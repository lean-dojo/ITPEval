-- Statement-only formalization of Logipedia corpus artifact exp.eq_exp
-- (catalog title "exp.eq_exp"): at every pair of natural arguments, the
-- exponentiation function is Leibniz-equal to the natural-type filter of its
-- body at the same exponent. This file contains no proof.

{-# OPTIONS --safe #-}

module eq_exp where

open import Agda.Primitive using (Level; lsuc)
open import Agda.Builtin.Nat using (Nat)

Leibniz :
  {level : Level} ->
  (A : Set level) ->
  A ->
  A ->
  Set (lsuc level)
Leibniz {level} A x y =
  (P : A -> Set level) ->
  P x ->
  P y

module Statement
  (filter-nat-type : (A : Set) -> (Nat -> A) -> Nat -> A)
  (exp exp-body : Nat -> Nat -> Nat) where

  eq-exp : Set₁
  eq-exp =
    (n m : Nat) ->
    Leibniz
      Nat
      (exp n m)
      (filter-nat-type Nat (exp-body n) m)
