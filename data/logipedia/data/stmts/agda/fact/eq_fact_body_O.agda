-- Statement-only formalization of Logipedia corpus artifact fact.eq_fact_body_O
-- (catalog title "fact.eq_fact_body_O"): the factorial body at natural number
-- zero is Leibniz-equal to one. This file contains no proof.

{-# OPTIONS --safe #-}

module eq_fact_body_O where

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

  eq-fact-body-O : Set₁
  eq-fact-body-O =
    Leibniz Nat (fact-body zero) (suc zero)
