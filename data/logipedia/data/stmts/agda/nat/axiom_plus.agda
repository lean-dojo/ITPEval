-- Statement-only formalization of Logipedia corpus artifact nat.axiom_plus
-- (catalog title "nat.axiom_plus"): for every natural number, the addition
-- function at that number is related by the source equality proposition to
-- the addition body filtered at the same number. This file contains no proof.

{-# OPTIONS --safe #-}

module axiom_plus where

open import Agda.Builtin.Nat using (Nat)

module Statement
  (equal : (A : Set) -> A -> A -> Set)
  (filter-nat-type : (A : Set) -> (Nat -> A) -> Nat -> A)
  (plus plus-body : Nat -> Nat -> Nat) where

  axiom-plus : Set
  axiom-plus =
    (n : Nat) ->
    equal
      (Nat -> Nat)
      (plus n)
      (filter-nat-type (Nat -> Nat) plus-body n)
