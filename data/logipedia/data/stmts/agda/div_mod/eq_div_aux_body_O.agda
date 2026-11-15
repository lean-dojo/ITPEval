-- Statement-only formalization of Logipedia corpus artifact
-- div_mod.eq_div_aux_body_O (catalog title
-- "div_mod.eq_div_aux_body_O"): the auxiliary division body at natural index
-- zero is Leibniz-equal to the constant-zero binary natural-number function.
-- This file contains no proof.

{-# OPTIONS --safe #-}

module eq_div_aux_body_O where

open import Agda.Primitive using (Level; lsuc)
open import Agda.Builtin.Nat using (Nat; zero)

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
  (div-aux-body : Nat -> Nat -> Nat -> Nat) where

  eq-div-aux-body-O : Set₁
  eq-div-aux-body-O =
    Leibniz
      (Nat -> Nat -> Nat)
      (div-aux-body zero)
      (\ m n -> zero)
