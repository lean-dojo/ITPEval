-- Statement-only formalization of Logipedia corpus artifact fact.eq_fact_body_S
-- (catalog title "fact.eq_fact_body_S"): for every natural number, the
-- factorial body at its successor is Leibniz-equal to the factorial value at
-- that number multiplied by its successor. This file contains no proof.

{-# OPTIONS --safe #-}

module eq_fact_body_S where

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

  eq-fact-body-S : Set₁
  eq-fact-body-S =
    (n : Nat) ->
    Leibniz Nat (fact-body (suc n)) ((fact n) * (suc n))
