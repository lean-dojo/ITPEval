-- Statement-only formalization of Logipedia corpus artifact
-- div_mod.axiom_mod_aux (catalog title "div_mod.axiom_mod_aux"): for every
-- natural index, the auxiliary modulus function equals the filtered auxiliary
-- modulus body as a binary natural-number function. This file contains no proof.

{-# OPTIONS --safe #-}

module axiom_mod_aux where

open import Agda.Builtin.Nat using (Nat)

module Statement
  (equal : (A : Set) -> A -> A -> Set)
  (filter-nat-type : (A : Set) -> (Nat -> A) -> Nat -> A)
  (mod-aux mod-aux-body : Nat -> Nat -> Nat -> Nat) where

  axiom-mod-aux : Set
  axiom-mod-aux =
    (p : Nat) ->
    equal
      (Nat -> Nat -> Nat)
      (mod-aux p)
      (filter-nat-type (Nat -> Nat -> Nat) mod-aux-body p)
