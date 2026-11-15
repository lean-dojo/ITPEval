-- Statement-only formalization of Logipedia corpus artifact nat.sym_eq_eqb_body_S
-- (catalog title "nat.sym_eq_eqb_body_S"): for every natural number, the
-- natural eliminator returning false at zero and Boolean equality with the
-- predecessor at each successor is Leibniz-equal to the Boolean equality body
-- at that number's successor. This file contains no proof.

{-# OPTIONS --safe #-}

module sym_eq_eqb_body_S where

open import Agda.Primitive using (Level; lsuc)
open import Agda.Builtin.Nat using (Nat; suc)
open import Agda.Builtin.Bool using (Bool; false)

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
  (eqb eqb-body : Nat -> Nat -> Bool) where

  sym-eq-eqb-body-S : Set₁
  sym-eq-eqb-body-S =
    (n : Nat) ->
    Leibniz
      (Nat -> Bool)
      (\ m -> match-nat-type Bool false (\ q -> eqb n q) m)
      (eqb-body (suc n))
