-- Statement-only formalization of Logipedia corpus artifact permutation.axiom_invert_permut
-- (catalog title "permutation.axiom_invert_permut"): at every natural index,
-- the inverse-permutation function equals the natural-type filter of its body.
-- This file contains no proof.

{-# OPTIONS --safe #-}

module axiom_invert_permut where

open import Agda.Builtin.Nat using (Nat)

InversePermutation : Set
InversePermutation =
  (Nat -> Nat) -> Nat -> Nat

module Statement
  (equal : (A : Set) -> A -> A -> Set)
  (filter-nat-type : (A : Set) -> (Nat -> A) -> Nat -> A)
  (invert-permut invert-permut-body : Nat -> InversePermutation) where

  axiom-invert-permut : Set
  axiom-invert-permut =
    (n : Nat) ->
    equal
      InversePermutation
      (invert-permut n)
      (filter-nat-type InversePermutation invert-permut-body n)
