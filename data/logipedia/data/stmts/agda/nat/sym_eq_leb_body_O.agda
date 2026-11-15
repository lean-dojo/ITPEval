-- Statement-only formalization of Logipedia corpus artifact nat.sym_eq_leb_body_O
-- (catalog title "nat.sym_eq_leb_body_O"): the constant-true function on
-- natural numbers is Leibniz-equal to the Boolean less-than-or-equal body at
-- natural number zero. This file contains no proof.

{-# OPTIONS --safe #-}

module sym_eq_leb_body_O where

open import Agda.Primitive using (Level; lsuc)
open import Agda.Builtin.Nat using (Nat; zero)
open import Agda.Builtin.Bool using (Bool; true)

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
  (leb-body : Nat -> Nat -> Bool) where

  sym-eq-leb-body-O : Set₁
  sym-eq-leb-body-O =
    Leibniz
      (Nat -> Bool)
      (\ m -> true)
      (leb-body zero)
