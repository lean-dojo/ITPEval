-- Statement-only formalization of Logipedia corpus artifact
-- gcd.sym_eq_gcd_aux_body_O (catalog title "gcd.sym_eq_gcd_aux_body_O"):
-- the binary natural-number function returning its first argument is
-- Leibniz-equal to the auxiliary greatest-common-divisor body at natural
-- index zero. This file contains no proof.

{-# OPTIONS --safe #-}

module sym_eq_gcd_aux_body_O where

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
  (gcd-aux-body : Nat -> Nat -> Nat -> Nat) where

  sym-eq-gcd-aux-body-O : Set₁
  sym-eq-gcd-aux-body-O =
    Leibniz
      (Nat -> Nat -> Nat)
      (\ m n -> m)
      (gcd-aux-body zero)
