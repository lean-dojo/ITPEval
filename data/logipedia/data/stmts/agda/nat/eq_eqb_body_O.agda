-- Statement-only formalization of Logipedia corpus artifact nat.eq_eqb_body_O
-- (catalog title "nat.eq_eqb_body_O"): the Boolean equality body at natural
-- number zero is Leibniz-equal to the natural eliminator returning true at
-- zero and false at successors. This file contains no proof.

{-# OPTIONS --safe #-}

module eq_eqb_body_O where

open import Agda.Primitive using (Level; lsuc)
open import Agda.Builtin.Nat using (Nat; zero)
open import Agda.Builtin.Bool using (Bool; true; false)

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
  (match-nat-type : (A : Set) -> A -> (Nat -> A) -> Nat -> A)
  (eqb-body : Nat -> Nat -> Bool) where

  eq-eqb-body-O : Set₁
  eq-eqb-body-O =
    Leibniz
      (Nat -> Bool)
      (eqb-body zero)
      (\ m -> match-nat-type Bool true (\ q -> false) m)
