-- Statement-only formalization of Logipedia corpus artifact
-- permutation.axiom_invert_permut_body_O (catalog title
-- "permutation.axiom_invert_permut_body_O"): the inverse-permutation body at
-- zero equals the natural-valued function selected by Boolean equality with
-- the image of zero. This file contains no proof.

{-# OPTIONS --safe #-}

module axiom_invert_permut_body_O where

open import Agda.Builtin.Bool using (Bool)
open import Agda.Builtin.Nat using (Nat; zero)

InversePermutation : Set
InversePermutation =
  (Nat -> Nat) -> Nat -> Nat

module Statement
  (equal : (A : Set) -> A -> A -> Set)
  (eqb : Nat -> Nat -> Bool)
  (match-bool-type : (A : Set) -> A -> A -> Bool -> A)
  (invert-permut-body : Nat -> InversePermutation) where

  axiom-invert-permut-body-O : Set
  axiom-invert-permut-body-O =
    equal
      InversePermutation
      (invert-permut-body zero)
      (\ f m ->
        match-bool-type Nat zero zero (eqb m (f zero)))
