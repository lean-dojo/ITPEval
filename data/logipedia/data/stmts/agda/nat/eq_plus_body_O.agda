-- Statement-only formalization of Logipedia corpus artifact
-- nat.eq_plus_body_O (catalog title "nat.eq_plus_body_O"): the natural
-- addition body at zero is Leibniz-equal to the identity function on natural
-- numbers. This file contains no proof.

{-# OPTIONS --safe #-}

module eq_plus_body_O where

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

  eq-plus-body-O : Set₁
  eq-plus-body-O =
    Leibniz
      (Nat -> Nat)
      (plus-body zero)
      (\ m -> m)
