-- Statement-only formalization of Logipedia corpus artifact nat.sym_eq_eqb_body_O
-- (catalog title "nat.sym_eq_eqb_body_O"): the natural eliminator returning
-- true at zero and false at successors is Leibniz-equal to the Boolean
-- equality body at natural number zero. This file contains no proof.

{-# OPTIONS --safe #-}

module sym_eq_eqb_body_O where

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

  sym-eq-eqb-body-O : Set₁
  sym-eq-eqb-body-O =
    Leibniz
      (Nat -> Bool)
      (\ m -> match-nat-type Bool true (\ q -> false) m)
      (eqb-body zero)
