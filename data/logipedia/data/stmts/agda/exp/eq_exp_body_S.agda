-- Statement-only formalization of Logipedia corpus artifact exp.eq_exp_body_S
-- (catalog title "exp.eq_exp_body_S"): for every pair of natural numbers, the
-- exponentiation body at the successor of the second is Leibniz-equal to the
-- exponentiation value multiplied by the first. This file contains no proof.

{-# OPTIONS --safe #-}

module eq_exp_body_S where

open import Agda.Primitive using (Level; lsuc)
open import Agda.Builtin.Nat using (Nat; suc; _*_)

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
  (exp exp-body : Nat -> Nat -> Nat) where

  eq-exp-body-S : Set₁
  eq-exp-body-S =
    (n m : Nat) ->
    Leibniz Nat (exp-body n (suc m)) ((exp n m) * n)
