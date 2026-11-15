-- Statement-only formalization of Logipedia corpus artifact
-- div_mod.sym_eq_mod_aux_body_O (catalog title
-- "div_mod.sym_eq_mod_aux_body_O"): the binary natural-number function
-- returning its first argument is Leibniz-equal to the auxiliary modulus body
-- at natural index zero. This file contains no proof.

{-# OPTIONS --safe #-}

module sym_eq_mod_aux_body_O where

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

  sym-eq-mod-aux-body-O : Set₁
  sym-eq-mod-aux-body-O =
    Leibniz
      (Nat -> Nat -> Nat)
      (\ m n -> m)
      (mod-aux-body zero)
