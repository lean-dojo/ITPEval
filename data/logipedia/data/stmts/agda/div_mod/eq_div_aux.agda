-- Statement-only formalization of Logipedia corpus artifact
-- div_mod.eq_div_aux (catalog title "div_mod.eq_div_aux"): for every natural
-- index, the auxiliary division function is Leibniz-equal to the filtered
-- auxiliary division body as a binary natural-number function. This file
-- contains no proof.

{-# OPTIONS --safe #-}

module eq_div_aux where

open import Agda.Primitive using (Level; lsuc)
open import Agda.Builtin.Nat using (Nat)

Leibniz :
  {level : Level} ->
  (A : Set level) ->
  A ->
  A ->
  Set (lsuc level)
Leibniz A x y =
  (P : A -> Set _) ->
  P x ->
  P y

module Statement
  (filter-nat-type : (A : Set) -> (Nat -> A) -> Nat -> A)
  (div-aux div-aux-body : Nat -> Nat -> Nat -> Nat) where

  eq-div-aux : Set₁
  eq-div-aux =
    (p : Nat) ->
    Leibniz
      (Nat -> Nat -> Nat)
      (div-aux p)
      (filter-nat-type (Nat -> Nat -> Nat) div-aux-body p)
