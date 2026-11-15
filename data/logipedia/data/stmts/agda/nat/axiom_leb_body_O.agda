-- Statement-only formalization of Logipedia corpus artifact nat.axiom_leb_body_O
-- (catalog title "nat.axiom_leb_body_O"): the Boolean less-than-or-equal body
-- at natural number zero is related by the source equality proposition to the
-- constant-true function on natural numbers. This file contains no proof.

{-# OPTIONS --safe #-}

module axiom_leb_body_O where

open import Agda.Builtin.Nat using (Nat; zero)
open import Agda.Builtin.Bool using (Bool; true)

module Statement
  (equal : (A : Set) -> A -> A -> Set)
  (leb-body : Nat -> Nat -> Bool) where

  axiom-leb-body-O : Set
  axiom-leb-body-O =
    equal
      (Nat -> Bool)
      (leb-body zero)
      (\ m -> true)
