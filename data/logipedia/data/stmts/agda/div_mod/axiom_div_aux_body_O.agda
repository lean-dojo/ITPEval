-- Statement-only formalization of Logipedia corpus artifact
-- div_mod.axiom_div_aux_body_O (catalog title
-- "div_mod.axiom_div_aux_body_O"): the auxiliary division body at natural
-- index zero equals the constant-zero binary natural-number function. This
-- file contains no proof.

{-# OPTIONS --safe #-}

module axiom_div_aux_body_O where

open import Agda.Builtin.Nat using (Nat; zero)

module Statement
  (equal : (A : Set) -> A -> A -> Set)
  (div-aux-body : Nat -> Nat -> Nat -> Nat) where

  axiom-div-aux-body-O : Set
  axiom-div-aux-body-O =
    equal
      (Nat -> Nat -> Nat)
      (div-aux-body zero)
      (\ m n -> zero)
