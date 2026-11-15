-- Statement-only formalization of Logipedia corpus artifact
-- nat.axiom_plus_body_O (catalog title "nat.axiom_plus_body_O"): the addition
-- body at natural number zero is related by the source equality proposition
-- to the identity function on natural numbers. This file contains no proof.

{-# OPTIONS --safe #-}

module axiom_plus_body_O where

open import Agda.Builtin.Nat using (Nat; zero)

module Statement
  (equal : (A : Set) -> A -> A -> Set)
  (plus-body : Nat -> Nat -> Nat) where

  axiom-plus-body-O : Set
  axiom-plus-body-O =
    equal
      (Nat -> Nat)
      (plus-body zero)
      (\ m -> m)
