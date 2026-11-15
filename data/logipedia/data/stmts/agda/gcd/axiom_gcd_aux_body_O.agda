-- Statement-only formalization of Logipedia corpus artifact
-- gcd.axiom_gcd_aux_body_O (catalog title "gcd.axiom_gcd_aux_body_O"): the
-- auxiliary greatest-common-divisor body at natural index zero equals the
-- binary natural-number function returning its first argument. This file
-- contains no proof.

{-# OPTIONS --safe #-}

module axiom_gcd_aux_body_O where

open import Agda.Builtin.Nat using (Nat; zero)

module Statement
  (equal : (A : Set) -> A -> A -> Set)
  (gcd-aux-body : Nat -> Nat -> Nat -> Nat) where

  axiom-gcd-aux-body-O : Set
  axiom-gcd-aux-body-O =
    equal
      (Nat -> Nat -> Nat)
      (gcd-aux-body zero)
      (\ m n -> m)
