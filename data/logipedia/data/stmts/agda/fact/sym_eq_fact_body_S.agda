-- Statement-only formalization of Logipedia corpus artifact fact.sym_eq_fact_body_S
-- (catalog title "fact.sym_eq_fact_body_S"): for every natural number, the
-- factorial value at that number multiplied by its successor is Leibniz-equal
-- to the factorial body at its successor. This file contains no proof.

{-# OPTIONS --safe #-}

module sym_eq_fact_body_S where

open import Agda.Primitive using (Level; lsuc)
open import Agda.Builtin.Nat using (Nat; suc; _*_)

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
  (fact fact-body : Nat -> Nat) where

  sym-eq-fact-body-S : Set₁
  sym-eq-fact-body-S =
    (n : Nat) ->
    Leibniz Nat ((fact n) * (suc n)) (fact-body (suc n))
