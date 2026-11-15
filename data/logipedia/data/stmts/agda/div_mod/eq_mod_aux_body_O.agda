-- Statement-only formalization of Logipedia corpus artifact
-- div_mod.eq_mod_aux_body_O (catalog title "div_mod.eq_mod_aux_body_O"):
-- the auxiliary modulus body at natural index zero is Leibniz-equal to the
-- binary natural-number function returning its first argument. This file
-- contains no proof.

{-# OPTIONS --safe #-}

module eq_mod_aux_body_O where

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
  (mod-aux-body : Nat -> Nat -> Nat -> Nat) where

  eq-mod-aux-body-O : Set₁
  eq-mod-aux-body-O =
    Leibniz
      (Nat -> Nat -> Nat)
      (mod-aux-body zero)
      (\ m n -> m)
