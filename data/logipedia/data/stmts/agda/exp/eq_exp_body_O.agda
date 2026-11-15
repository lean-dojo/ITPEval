-- Statement-only formalization of Logipedia corpus artifact exp.eq_exp_body_O
-- (catalog title "exp.eq_exp_body_O"): for every natural number, the
-- exponentiation body at zero is Leibniz-equal to one. This file contains no
-- proof.

{-# OPTIONS --safe #-}

module eq_exp_body_O where

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

  eq-exp-body-O : Set₁
  eq-exp-body-O =
    (n : Nat) ->
    Leibniz Nat (exp-body n zero) (suc zero)
