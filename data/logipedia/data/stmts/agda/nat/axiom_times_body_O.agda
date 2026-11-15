-- Statement-only formalization of Logipedia corpus artifact
-- nat.axiom_times_body_O (catalog title "nat.axiom_times_body_O"): the
-- multiplication body at natural number zero is related by the source equality
-- proposition to the constant-zero function. This file contains no proof.

{-# OPTIONS --safe #-}

module axiom_times_body_O where

open import Agda.Builtin.Nat using (Nat; zero)

module Statement
  (equal : (A : Set) -> A -> A -> Set)
  (times-body : Nat -> Nat -> Nat) where

  axiom-times-body-O : Set
  axiom-times-body-O =
    equal
      (Nat -> Nat)
      (times-body zero)
      (\ m -> zero)
