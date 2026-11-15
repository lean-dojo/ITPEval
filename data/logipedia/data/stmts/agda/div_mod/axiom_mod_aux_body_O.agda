-- Statement-only formalization of Logipedia corpus artifact
-- div_mod.axiom_mod_aux_body_O (catalog title
-- "div_mod.axiom_mod_aux_body_O"): the auxiliary modulus body at natural
-- index zero equals the binary natural-number function returning its first
-- argument. This file contains no proof.

{-# OPTIONS --safe #-}

module axiom_mod_aux_body_O where

open import Agda.Builtin.Nat using (Nat; zero)

module Statement
  (equal : (A : Set) -> A -> A -> Set)
  (mod-aux-body : Nat -> Nat -> Nat -> Nat) where

  axiom-mod-aux-body-O : Set
  axiom-mod-aux-body-O =
    equal
      (Nat -> Nat -> Nat)
      (mod-aux-body zero)
      (\ m n -> m)
