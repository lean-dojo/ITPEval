-- Statement-only formalization of Logipedia corpus artifact
-- nat.sym_eq_minus_body_O (catalog title "nat.sym_eq_minus_body_O"): the
-- constant-zero function on natural numbers is Leibniz-equal to the natural
-- subtraction body at zero. This file contains no proof.

{-# OPTIONS --safe #-}

module sym_eq_minus_body_O where

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
  (minus-body : Nat -> Nat -> Nat) where

  sym-eq-minus-body-O : Set₁
  sym-eq-minus-body-O =
    Leibniz
      (Nat -> Nat)
      (\ m -> zero)
      (minus-body zero)
