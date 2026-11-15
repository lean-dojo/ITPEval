-- Statement-only formalization of Logipedia corpus artifact fact.axiom_fact_body_O
-- (catalog title "fact.axiom_fact_body_O"): the factorial body at natural
-- number zero equals one. This file contains no proof.

{-# OPTIONS --safe #-}

module axiom_fact_body_O where

open import Agda.Builtin.Nat using (Nat; zero; suc)

module Statement
  (equal : (A : Set) -> A -> A -> Set)
  (fact-body : Nat -> Nat) where

  axiom-fact-body-O : Set
  axiom-fact-body-O =
    equal Nat (fact-body zero) (suc zero)
