-- Statement-only formalization of Logipedia corpus artifact fact.axiom_fact_body_S
-- (catalog title "fact.axiom_fact_body_S"): for every natural number, the
-- factorial body at its successor equals the factorial value at that number
-- multiplied by its successor. This file contains no proof.

{-# OPTIONS --safe #-}

module axiom_fact_body_S where

open import Agda.Builtin.Nat using (Nat; suc; _*_)

module Statement
  (equal : (A : Set) -> A -> A -> Set)
  (fact fact-body : Nat -> Nat) where

  axiom-fact-body-S : Set
  axiom-fact-body-S =
    (n : Nat) ->
    equal Nat (fact-body (suc n)) ((fact n) * (suc n))
