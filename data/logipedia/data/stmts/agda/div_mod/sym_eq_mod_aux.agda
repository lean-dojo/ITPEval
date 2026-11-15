-- Statement-only formalization of Logipedia corpus artifact
-- div_mod.sym_eq_mod_aux (catalog title "div_mod.sym_eq_mod_aux"): for every
-- natural index, the filtered auxiliary modulus body is Leibniz-equal to the
-- auxiliary modulus function as a binary natural-number function. This file
-- contains no proof.

{-# OPTIONS --safe #-}

module sym_eq_mod_aux where

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
  (mod-aux mod-aux-body : Nat -> Nat -> Nat -> Nat) where

  sym-eq-mod-aux : Set₁
  sym-eq-mod-aux =
    (p : Nat) ->
    Leibniz
      (Nat -> Nat -> Nat)
      (filter-nat-type (Nat -> Nat -> Nat) mod-aux-body p)
      (mod-aux p)
