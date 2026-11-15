-- Statement-only formalization of Logipedia corpus artifact fact.sym_eq_fact_body_O
-- (catalog title "fact.sym_eq_fact_body_O"): one is Leibniz-equal to the
-- factorial body at natural number zero. This file contains no proof.

{-# OPTIONS --safe #-}

module sym_eq_fact_body_O where

open import Agda.Primitive using (Level; lsuc)
open import Agda.Builtin.Nat using (Nat; zero; suc)

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

module Statement (fact-body : Nat -> Nat) where

  sym-eq-fact-body-O : Set₁
  sym-eq-fact-body-O =
    Leibniz Nat (suc zero) (fact-body zero)
