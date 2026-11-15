-- Statement-only formalization of Logipedia corpus artifact
-- nat.eq_minus_body_O (catalog title "nat.eq_minus_body_O"): the natural
-- subtraction body at zero is Leibniz-equal to the constant-zero function on
-- natural numbers. This file contains no proof.

{-# OPTIONS --safe #-}

module eq_minus_body_O where

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

  eq-minus-body-O : Set₁
  eq-minus-body-O =
    Leibniz
      (Nat -> Nat)
      (minus-body zero)
      (\ m -> zero)
