-- Statement-only formalization of Logipedia corpus artifact
-- div_mod.eq_mod_aux (catalog title "div_mod.eq_mod_aux"): for every natural
-- index, the auxiliary modulus function is Leibniz-equal to the filtered
-- auxiliary modulus body as a binary natural-number function. This file
-- contains no proof.

{-# OPTIONS --safe #-}

module eq_mod_aux where

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

  eq-mod-aux : Set₁
  eq-mod-aux =
    (p : Nat) ->
    Leibniz
      (Nat -> Nat -> Nat)
      (mod-aux p)
      (filter-nat-type (Nat -> Nat -> Nat) mod-aux-body p)
