-- Statement-only formalization of Logipedia corpus artifact nat.sym_eq_plus
-- (catalog title "nat.sym_eq_plus"): at every natural argument, the
-- natural-type filter of the addition body is Leibniz-equal to the addition
-- function at the same argument. This file contains no proof.

{-# OPTIONS --safe #-}

module sym_eq_plus where

open import Agda.Primitive using (Level; lsuc)
open import Agda.Builtin.Nat using (Nat)

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
  (filter-nat-type : (A : Set) -> (Nat -> A) -> Nat -> A)
  (plus plus-body : Nat -> Nat -> Nat) where

  sym-eq-plus : Set₁
  sym-eq-plus =
    (n : Nat) ->
    Leibniz
      (Nat -> Nat)
      (filter-nat-type (Nat -> Nat) plus-body n)
      (plus n)
