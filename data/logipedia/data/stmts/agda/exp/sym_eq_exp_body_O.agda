-- Statement-only formalization of Logipedia corpus artifact
-- exp.sym_eq_exp_body_O (catalog title "exp.sym_eq_exp_body_O"): for every
-- natural number, one is Leibniz-equal to the exponentiation body at zero.
-- This file contains no proof.

{-# OPTIONS --safe #-}

module sym_eq_exp_body_O where

open import Agda.Primitive using (Level; lsuc)
open import Agda.Builtin.Nat using (Nat; zero; suc)

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
  (exp-body : Nat -> Nat -> Nat) where

  sym-eq-exp-body-O : Set₁
  sym-eq-exp-body-O =
    (n : Nat) ->
    Leibniz Nat (suc zero) (exp-body n zero)
