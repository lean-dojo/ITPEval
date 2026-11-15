-- Statement-only formalization of Logipedia corpus artifact
-- permutation.axiom_invert_permut_body_S (catalog title
-- "permutation.axiom_invert_permut_body_S"): at each successor index, the
-- inverse-permutation body returns that successor when its argument equals the
-- image of the successor, and otherwise uses the preceding inverse-permutation
-- function. This file contains no proof.

{-# OPTIONS --safe #-}

module axiom_invert_permut_body_S where

open import Agda.Builtin.Bool using (Bool)
open import Agda.Builtin.Nat using (Nat; suc)

InversePermutation : Set
InversePermutation =
  (Nat -> Nat) -> Nat -> Nat

module Statement
  (equal : (A : Set) -> A -> A -> Set)
  (eqb : Nat -> Nat -> Bool)
  (match-bool-type : (A : Set) -> A -> A -> Bool -> A)
  (invert-permut invert-permut-body : Nat -> InversePermutation) where

  axiom-invert-permut-body-S : Set
  axiom-invert-permut-body-S =
    (n : Nat) ->
    equal
      InversePermutation
      (invert-permut-body (suc n))
      (\ f m ->
        match-bool-type
          Nat
          (suc n)
          (invert-permut n f m)
          (eqb m (f (suc n))))
