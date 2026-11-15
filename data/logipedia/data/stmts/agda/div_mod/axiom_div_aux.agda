-- Statement-only formalization of Logipedia corpus artifact
-- div_mod.axiom_div_aux (catalog title "div_mod.axiom_div_aux"): for every
-- natural index, the auxiliary division function equals the filtered auxiliary
-- division body as a binary natural-number function. This file contains no proof.

{-# OPTIONS --safe #-}

module axiom_div_aux where

open import Agda.Builtin.Nat using (Nat)

module Statement
  (equal : (A : Set) -> A -> A -> Set)
  (filter-nat-type : (A : Set) -> (Nat -> A) -> Nat -> A)
  (div-aux div-aux-body : Nat -> Nat -> Nat -> Nat) where

  axiom-div-aux : Set
  axiom-div-aux =
    (p : Nat) ->
    equal
      (Nat -> Nat -> Nat)
      (div-aux p)
      (filter-nat-type (Nat -> Nat -> Nat) div-aux-body p)
