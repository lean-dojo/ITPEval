-- Statement-only formalization of Logipedia corpus artifact
-- nat.sym_eq_plus_body_O (catalog title "nat.sym_eq_plus_body_O"): the
-- identity function on natural numbers is Leibniz-equal to the natural
-- addition body at zero. This file contains no proof.

{-# OPTIONS --safe #-}

module sym_eq_plus_body_O where

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
  (plus-body : Nat -> Nat -> Nat) where

  sym-eq-plus-body-O : Set₁
  sym-eq-plus-body-O =
    Leibniz
      (Nat -> Nat)
      (\ m -> m)
      (plus-body zero)
