-- Statement-only formalization of Logipedia corpus artifact
-- nat.axiom_minus_body_O (catalog title "nat.axiom_minus_body_O"): the
-- subtraction body at natural number zero is related by the source equality
-- proposition to the constant-zero function. This file contains no proof.

{-# OPTIONS --safe #-}

module axiom_minus_body_O where

open import Agda.Builtin.Nat using (Nat; zero)

module Statement
  (equal : (A : Set) -> A -> A -> Set)
  (minus-body : Nat -> Nat -> Nat) where

  axiom-minus-body-O : Set
  axiom-minus-body-O =
    equal
      (Nat -> Nat)
      (minus-body zero)
      (\ m -> zero)
