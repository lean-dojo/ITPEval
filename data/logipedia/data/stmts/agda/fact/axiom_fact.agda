-- Statement-only formalization of Logipedia corpus artifact fact.axiom_fact
-- (catalog title "fact.axiom_fact"): at every natural argument, the factorial
-- function equals the natural-type filter of its body at the same argument.
-- This file contains no proof.

{-# OPTIONS --safe #-}

module axiom_fact where

open import Agda.Builtin.Nat using (Nat)

module Statement
  (equal : (A : Set) -> A -> A -> Set)
  (filter-nat-type : (A : Set) -> (Nat -> A) -> Nat -> A)
  (fact fact-body : Nat -> Nat) where

  axiom-fact : Set
  axiom-fact =
    (n : Nat) ->
    equal
      Nat
      (fact n)
      (filter-nat-type Nat fact-body n)
