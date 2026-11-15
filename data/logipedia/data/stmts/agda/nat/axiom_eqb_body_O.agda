-- Statement-only formalization of Logipedia corpus artifact nat.axiom_eqb_body_O
-- (catalog title "nat.axiom_eqb_body_O"): the Boolean equality body at natural
-- number zero is related by the source equality proposition to the natural
-- eliminator returning true at zero and false at successors. This file contains
-- no proof.

{-# OPTIONS --safe #-}

module axiom_eqb_body_O where

open import Agda.Builtin.Nat using (Nat; zero)
open import Agda.Builtin.Bool using (Bool; true; false)

module Statement
  (equal : (A : Set) -> A -> A -> Set)
  (match-nat-type : (A : Set) -> A -> (Nat -> A) -> Nat -> A)
  (eqb-body : Nat -> Nat -> Bool) where

  axiom-eqb-body-O : Set
  axiom-eqb-body-O =
    equal
      (Nat -> Bool)
      (eqb-body zero)
      (\ m -> match-nat-type Bool true (\ q -> false) m)
