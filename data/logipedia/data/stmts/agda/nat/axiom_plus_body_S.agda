-- Statement-only formalization of Logipedia corpus artifact
-- nat.axiom_plus_body_S (catalog title "nat.axiom_plus_body_S"): for every
-- natural number, the addition body at its successor is related by the source
-- equality proposition to the successor of addition at that number. This file
-- contains no proof.

{-# OPTIONS --safe #-}

module axiom_plus_body_S where

open import Agda.Builtin.Nat using (Nat; suc)

module Statement
  (equal : (A : Set) -> A -> A -> Set)
  (plus plus-body : Nat -> Nat -> Nat) where

  axiom-plus-body-S : Set
  axiom-plus-body-S =
    (n : Nat) ->
    equal
      (Nat -> Nat)
      (plus-body (suc n))
      (\ m -> suc (plus n m))
